#![allow(unused)]
use std::hint::unreachable_unchecked;

use super::utils::expression_variant;
use super::BoundsCheckError;
use crate::{
    Arena, Block, EntryPoint, Expression, FastHashMap, FastHashSet, GlobalVariable, Handle,
    LocalVariable, Range, Statement, SwitchCase,
};

mod expression_visitor;
use expression_visitor::ExpressionVisitor;

mod statement_visitor;
use statement_visitor::StatementVisitor;

mod var_visitor;
use super::AddressSpacesToCheck;
use var_visitor::{VarVisitor, VarVisitorResult};

/****************************
 *      VisitorError        *
 * **************************/
#[derive(Clone, Debug, thiserror::Error)]
pub enum VisitorError {
    #[error("{0}")]
    BadHandle(#[from] crate::arena::BadHandle),
    #[error("Found a local variable reference with no active function")]
    LocalOutsideFunction,
    #[error("Index will overflow")]
    IndexOverflow,
    #[error("Invalid expression kind for pointer: {0}.")]
    InvalidPointerKind(&'static str),
    #[error("{0} outside function context.")]
    NotInFunction(&'static str),
    #[error("Expression stack is empty")]
    EmptyExpressionStack,
    #[error("Active expression not found")]
    InvalidActiveExpression,
    #[error("Fall through is not supported in switch statements")]
    FallThroughNotSupported,
    #[error("{0} Not Found")]
    NotFound(&'static str),
    #[error("Not implemented: {0}")]
    NotImplemented(&'static str),
    #[error("The TrackedRead::CallResult contains an expression that is not a CallResult")]
    NotCallResult,
}

impl VisitorError {
    /// Constructor for [`VisitorError::BadHandle`]
    ///
    /// [`VisitorError::BadHandle`]: crate::VisitorError::BadHandle
    #[cold] // Errors are unlikely!
    fn bad_handle(handle: Handle<Expression>) -> Self {
        Self::BadHandle(crate::arena::BadHandle::new(handle))
    }
}

/****************************
 *          Enums!          *
 * **************************/

/// Used by `ModuleStatementBuilder::visit_and_update` to inform which
/// read set should be updated.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ScopeKind {
    ControlFlow,
    StoreRead,
    RetRead,
}

/// Represents whether the expression resides in the local variable or global variables.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum VarKind {
    Local(Handle<Expression>),
    Global(Handle<Expression>),
}

/// A MarkedExprKey is the key for marked expressions.
#[derive(Clone, Copy, Hash, Eq, PartialEq)]
enum MarkedExprKey {
    GlobalVariable(Handle<GlobalVariable>),
    /// A local variable belonging to an expression in the module's function corresponding to the handle.
    FunctionLocal(Handle<crate::Function>, Handle<LocalVariable>),
    /// A local variable belonging to an expression in the module's entry point corresponding to the index.
    EntryPointLocal(EntryPointIndex, Handle<LocalVariable>),

    /// A call result expression corresponding to a function.
    FnCallResult(Handle<crate::Function>, Handle<Expression>),
    /// An expression in an entry point
    EpCallResult(EntryPointIndex, Handle<Expression>),

    /// An argument to an entry point
    EntryPointArgument(EntryPointIndex, u32),

    /// An argument to a function
    FunctionArgument(Handle<crate::Function>, u32),

    /// A function call (marked ONLY by other functions that have a corresponding `CallResult` that is marked.
    Function(Handle<crate::Function>),
}

trait IntoMarkedKey {
    #[allow(clippy::wrong_self_convention)]
    fn as_marked_key_with(self, path: &StatementPathPart) -> MarkedExprKey;
}

macro_rules! as_marked_key_impl {
    ($variant:expr, $ty:ty) => {
        impl IntoMarkedKey for $ty {
            fn as_marked_key_with(self, _: &StatementPathPart) -> MarkedExprKey {
                $variant(self)
            }
        }
    };
    ($fn_variant:expr, $ep_variant:expr, $ty:ty) => {
        impl IntoMarkedKey for $ty {
            fn as_marked_key_with(self, path: &StatementPathPart) -> MarkedExprKey {
                match *path {
                    StatementPathPart::Function(f) => $fn_variant(f, self),
                    StatementPathPart::EntryPoint(e) => $ep_variant(e, self),
                    _ => unreachable!(),
                }
            }
        }
    };
}

as_marked_key_impl!(MarkedExprKey::GlobalVariable, Handle<GlobalVariable>);
as_marked_key_impl!(
    MarkedExprKey::FunctionLocal,
    MarkedExprKey::EntryPointLocal,
    Handle<LocalVariable>
);
// Specifically for call result
as_marked_key_impl!(
    MarkedExprKey::FnCallResult,
    MarkedExprKey::EpCallResult,
    Handle<Expression>
);
as_marked_key_impl!(
    MarkedExprKey::FunctionArgument,
    MarkedExprKey::EntryPointArgument,
    u32
);
as_marked_key_impl!(MarkedExprKey::Function, Handle<crate::Function>);

bitflags::bitflags! {
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    struct ControlFlags: u8 {
        const BREAK =  0x1;
        const CONTINUE = 0x2;
        const RETURN =  0x4;
        const KILL = 0x8;
    }
}
impl Default for ControlFlags {
    fn default() -> Self {
        ControlFlags::empty()
    }
}

#[derive(Default)]
struct FunctionProperties {
    // Global variables written in the function (this can also be computed from the module info.)
    glbl_writes: FastHashSet<Handle<GlobalVariable>>,
    /// Function arguments that are written to by this function.
    arg_writes: FastHashSet<u32>,

    /// The map of expressions to the sub-expressions they depend on.
    subexpr_map: FastHashMap<Handle<Expression>, std::cell::RefCell<FastHashSet<TrackedVar>>>,

    /// This is the set of expressions that contain access indices (either themselves or in their sub-expressions)
    exprs_with_accesses: FastHashSet<Handle<Expression>>,

    /// The set of global variables, function arguments, and function results that are used as array indices in array accesses.
    index_access_dependencies: FastHashSet<TrackedVar>,

    /// The set of variables that influence the return value of the expression.
    ///
    /// This is computed so that later, if the result of this expression influences any array accesses,
    /// then we can mark all expressions that it influences as also needing to be tracked.
    ///
    /// This has to be done as a final pass.
    retval_dependencies: FastHashSet<TrackedVar>,

    // Whether there are any access indices in this function
    has_access_indices: bool,

    /// A map of call expressions to the expressions that comprise their call.
    call_dependencies: FastHashMap<Handle<Expression>, Vec<Handle<Expression>>>,

    // When we see a return statement, then this is immediately set to `Some(FastHashSet::default())`
    // Store statements that flow into vars marked in this arena are also added to this arena.
    fn_ret_cf_conditions: VarSet,

    is_marked: bool,
}

impl FunctionProperties {
    fn merge_from_statement_properties(&mut self, props: &StatementProperties) {
        self.glbl_writes.extend(props.glbl_writes.iter());
        self.arg_writes.extend(props.arg_writes.iter());
        self.has_access_indices |= props.has_expr_access;
    }
}

/// Sets of variables that are read from.
#[derive(Debug, Clone, Default)]
struct VarSet {
    /// Global variables
    gvars: FastHashSet<Handle<GlobalVariable>>,
    /// Global Constants
    constants: FastHashSet<Handle<crate::Constant>>,
    /// Global Overrides
    overrides: FastHashSet<Handle<crate::Override>>,
    /// Local Variables
    lvars: FastHashSet<Handle<LocalVariable>>,
    /// Function Arguments
    function_args: FastHashSet<u32>,

    /// Function Results. This includes both the function and the expression
    function_calls: FastHashSet<Handle<crate::Function>>,

    /// Handles in this set correspond to an expression in the function's arena, and
    /// are always a `CallResult`.
    call_results: FastHashSet<Handle<Expression>>,
}

impl VarSet {
    fn merge_with_other(&mut self, other: &VarSet) {
        self.gvars.extend(other.gvars.iter());
        self.constants.extend(other.constants.iter());
        self.overrides.extend(other.overrides.iter());
        self.lvars.extend(other.lvars.iter());
        self.function_args.extend(other.function_args.iter());
        self.function_calls.extend(other.function_calls.iter());
        self.call_results.extend(other.call_results.iter());
    }

    fn is_empty(&mut self) -> bool {
        self.gvars.is_empty()
            && self.lvars.is_empty()
            && self.function_args.is_empty()
            && self.function_calls.is_empty()
            && self.call_results.is_empty()
            && self.constants.is_empty()
            && self.overrides.is_empty()
    }
}

macro_rules! varset_insert_impl {
    ($name:ident, $ty:ty) => {
        impl VarSetInsert<$ty> for VarSet {
            #[doc = concat!("Inserts `item` into `self.", stringify!($name), "`")]
            fn insert(&mut self, item: $ty) {
                self.$name.insert(item);
            }
        }
    };
    ($($name:ident, $ty:ty),+ $(,)?) => {
        $(varset_insert_impl!($name, $ty);)+
    };
}
trait VarSetInsert<T> {
    fn insert(&mut self, handle: T);
}

varset_insert_impl! {
    gvars, Handle<GlobalVariable>,
    constants, Handle<crate::Constant>,
    overrides, Handle<crate::Override>,
    lvars, Handle<LocalVariable>,
    function_args, u32,
    function_calls, Handle<crate::Function>,
    call_results, Handle<Expression>,
}

impl VarSetInsert<TrackedVar> for VarSet {
    fn insert(&mut self, read: TrackedVar) {
        match read {
            TrackedVar::GlobalVariable(g) => self.gvars.insert(g),
            TrackedVar::LocalVariable(l) => self.lvars.insert(l),
            TrackedVar::FunctionArgument(a) => self.function_args.insert(a),
            TrackedVar::CallResult(r) => self.call_results.insert(r),
        };
    }
}

#[derive(Debug, Clone, Default)]
struct StatementProperties {
    /// Var set for variables that drive control flow for the statement.
    control_flow_vars: VarSet,
    /// Var set for variables that store statements depend on.
    store_reads: VarSet,

    /// Variables that are written to in this statement (sub-statements if this is a block).
    glbl_writes: FastHashSet<Handle<GlobalVariable>>,
    lcl_writes: FastHashSet<Handle<LocalVariable>>,
    arg_writes: FastHashSet<u32>,

    has_expr_access: bool,

    /// Whether this statement is guaranteed to terminate the block.
    ///
    /// N.B. this may have false negatives.  E.g, if we saw ``if (true) { return;} else {...}``,
    /// then the `if` statement would not be marked as a terminator even though it
    /// is guaranteed to be.
    ///
    /// That is, we don't do crazy static analysis when computing this.
    /// We just do a simple check to see if all paths have a terminator (regardless of whether or not all paths are reachable)
    is_terminator: bool,
    /// The control flow
    cf_flags: ControlFlags,

    /// There is a function call in this statement
    has_call: bool,

    /// Whether the statement has been marked as requiring to be visited by the visitor.
    marked: bool,
}

trait HasWrites {
    fn iter_glbl_writes(&self) -> impl Iterator<Item = &Handle<GlobalVariable>>;
    fn iter_lcl_writes(&self) -> impl Iterator<Item = &Handle<LocalVariable>>;
    fn iter_arg_writes(&self) -> impl Iterator<Item = &u32>;
}
trait TrackedStoreContainer {
    fn stores_to_marked(
        &self,
        marked: &FastHashSet<MarkedExprKey>,
        enclosed_path: &StatementPathPart,
    ) -> bool;
}

impl<T: HasWrites> TrackedStoreContainer for T {
    fn stores_to_marked(
        &self,
        marked: &FastHashSet<MarkedExprKey>,
        enclosed_path: &StatementPathPart,
    ) -> bool {
        self.iter_glbl_writes()
            .any(|g| marked.contains(&MarkedExprKey::GlobalVariable(*g)))
            || self
                .iter_lcl_writes()
                .any(|l| marked.contains(&l.as_marked_key_with(enclosed_path)))
            || self
                .iter_arg_writes()
                .any(|a| marked.contains(&a.as_marked_key_with(enclosed_path)))
    }
}

impl HasWrites for StatementProperties {
    #[inline]
    fn iter_glbl_writes(&self) -> impl Iterator<Item = &Handle<GlobalVariable>> {
        self.glbl_writes.iter()
    }
    #[inline]
    fn iter_lcl_writes(&self) -> impl Iterator<Item = &Handle<LocalVariable>> {
        self.lcl_writes.iter()
    }
    #[inline]
    fn iter_arg_writes(&self) -> impl Iterator<Item = &u32> {
        self.arg_writes.iter()
    }
}

impl HasWrites for FunctionProperties {
    #[inline]
    fn iter_glbl_writes(&self) -> impl Iterator<Item = &Handle<GlobalVariable>> {
        self.glbl_writes.iter()
    }

    #[inline]
    fn iter_lcl_writes(&self) -> impl Iterator<Item = &Handle<LocalVariable>> {
        std::iter::empty()
    }

    #[inline]
    fn iter_arg_writes(&self) -> impl Iterator<Item = &u32> {
        self.arg_writes.iter()
    }
}

impl StatementProperties {
    /// Mark this statement, returning whether or not it was marked.
    pub(crate) fn mark(&mut self) -> bool {
        std::mem::replace(&mut self.marked, true)
    }

    /// Return whether or not this statement is marked.
    #[inline]
    pub const fn is_marked(&self) -> bool {
        self.marked
    }
    /// Merges the writes for glbl, lcl, and args. Also merges `has_expr_access` using logical OR, and `cf_flags` using bitwise OR.
    fn merge_with(&mut self, other: &Self) {
        // Joining two properties ONLY joins the variables that are written to, along with whether it contains an expr access.
        // It does not join the control flow variables.
        self.glbl_writes.extend(other.glbl_writes.iter());
        self.lcl_writes.extend(other.lcl_writes.iter());
        self.arg_writes.extend(other.arg_writes.iter());
        self.has_expr_access |= other.has_expr_access;
        self.cf_flags |= other.cf_flags;
        self.has_call |= other.has_call;
    }

    /// Return whether or not this statement may need to be visited.
    ///
    /// It may need to be visited if it contains an expr access, a function call, contains any writes, or has any control flow statements within.
    fn may_need_visit(&self) -> bool {
        self.has_expr_access
            || self.has_call
            || !(self.cf_flags.is_empty()
                && self.glbl_writes.is_empty()
                && self.lcl_writes.is_empty()
                && self.arg_writes.is_empty())
    }

    const fn has_ret(&self) -> bool {
        self.cf_flags.contains(ControlFlags::RETURN)
    }

    const fn has_break_or_continue(&self) -> bool {
        self.cf_flags
            .intersects(ControlFlags::BREAK.union(ControlFlags::CONTINUE))
    }

    const fn has_break(&self) -> bool {
        self.cf_flags.contains(ControlFlags::BREAK)
    }

    const fn has_continue(&self) -> bool {
        self.cf_flags.contains(ControlFlags::CONTINUE)
    }
}

#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
// These are all of the statement variants that can contain other statements.
// We can build up a path of these statements..
enum StatementPathPart {
    /// The index of the function
    EntryPoint(EntryPointIndex),
    // The handle of the function
    Function(Handle<crate::Function>),
    // The index in a block
    Index(usize),

    /// The `accept` block of an `If` statement.
    Accept,

    // The `reject` block of an `If` statement.
    Reject,

    /// For Switch statements, the index in the [`Switch::cases`] vector.
    ///
    /// [`Switch::cases`]: crate::Statement::Switch::cases
    Case(usize),

    /// The `loop body` for the loop.
    LoopBody(usize),

    /// The `loop continuing` for the loop.
    LoopContinuing(usize),
}

/// This is a type wrapper around an index corresponding to an Entry Point.
#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash, Ord, PartialOrd)]
#[repr(transparent)]
struct EntryPointIndex(usize);

impl From<EntryPointIndex> for usize {
    fn from(index: EntryPointIndex) -> Self {
        index.0
    }
}

impl From<usize> for EntryPointIndex {
    fn from(index: usize) -> Self {
        EntryPointIndex(index)
    }
}

/// ModuleStatementBuilder is the first phase of the visitor.
///
/// In step 1, we visit every expression in each function's arena. Step 1 is accomplished by [`VarVisitor`].
/// For every expression, we compute two things:
///     - The set of expressions in this expression's sub-expression tree.
///     - Whether any of the expressions in tree are used to index into a buffer that needs to be checked, based on the provided [`AddressSpacesToCheck`].
///
/// In step 2, we visit the statements in each function's arena.
/// For every statement, we...
///     - Mark whether any of the expressions in the statement contain a buffer access that needs to be checked, based on the results of step 1.
///     - If the statement contains a modification to a variable, mark the set of `GlobalVariable`, `LocalVariable`, and `FunctionArgument` expressions that the modification depends on,
///     computed by iterating through the set of dependent expressions for the `value` that is being stored, as well as any expressions used to index into the variable being stored to.
///     - If the statement has any control flow, mark the set of expressions that the control flow depends on. For loops, this includes all expressions that are used to compute the loop condition,
///     as well as *any* expression in a conditional that contains a `break` or `continue` statement targeting the loop. For switch statements, this is just the selector, while for `if` statements, this is just the condition.
///     - For `return` statements, we also mark the set of expressions that the return value depends on. We also mark, for the function containing the return statement, the of expressions influencing control flow.
///
/// At the end of step 2, we will have:
/// For store statements, the set of `TrackedVars` that the store depends on.
/// For control flow statements, the set of `TrackedVars` that the control flow depends on, including indirectly through `continue`, `break`
/// For the function, the set of `TrackedVars` that direct control flow of return statements within
///
/// In step 3, we mark all `TrackedVar`s that must be tracked for bounds checking. This is done by continually looping through each function's arena, and marking an expression if it
/// - Is used to compute an access index
/// - Is a dependency of a store statement to a `TrackedExpression` that has been marked
/// - Is a dependency of a control flow statement that contains an access index or a store to a marked expression.
/// - It is an argument to a function call where either
///    - The function call's associated FunctionArgument is marked
///    - The function call's associated CallResult is marked and the argument FunctionArgument is marked as a retval dependency.
///
/// Note that step 3 is implemented by `ModuleStatementBuilderPhase2`, as it overrides the StatementVisitor in a different manner.
///
/// [`VarVisitor`]: super::VarVisitor
/// [`AddressSpacesToCheck`]: super::AddressSpacesToCheck
struct ModuleStatementBuilder<'module> {
    // The current path in the module.
    current_path: Vec<StatementPathPart>,
    // Statement map.
    statement_map: FastHashMap<Vec<StatementPathPart>, StatementProperties>,

    current_properties: StatementProperties,

    /// A map from functions to the computed reads from `VarVisitor`
    fn_reads: FastHashMap<Handle<crate::Function>, FunctionProperties>,

    /// A map from entry points to the computed reads from `VarVisitor`
    ep_reads: FastHashMap<EntryPointIndex, FunctionProperties>,

    // The module.
    module: &'module crate::Module,

    // the module info
    module_info: &'module crate::valid::ModuleInfo,

    /// Expressions that are marked are those that are used to compute an access index,
    /// store to a marked expression,
    /// or are used as a control flow expression for a statement that contains either of the above.
    marked_exprs: FastHashSet<MarkedExprKey>,

    address_space_config: AddressSpacesToCheck,

    // When we see a break statement, then this is immediately set to `Some(FastHashSet::default())`.
    loop_cf_conditions: Option<VarSet>,
}

/// Expands to a form that gets the current properties, either mutably or immutably,
/// depending on the form in which it was called.
macro_rules! get_cur_fn_props {
    ($self:ident, $get_method:ident) => {
        match $self.current_path.first() {
            Some(&StatementPathPart::EntryPoint(ref e)) => $self
                .ep_reads
                .$get_method(e)
                .ok_or_else(|| VisitorError::NotFound("Entry Point")),
            Some(&StatementPathPart::Function(ref f)) => $self
                .fn_reads
                .$get_method(f)
                .ok_or_else(|| VisitorError::NotFound("Function")),
            _ => Err(VisitorError::NotInFunction(
                "Attempt to get function properties",
            )),
        }
    };
}

impl<'module> ModuleStatementBuilder<'module> {
    /// Propagates the control flow dependencies up the function hierarchy.
    ///
    /// For returns, marks the return control flow dependencies for the function.
    /// For loops, merges the control flow dependencies with the loop's control flow dependencies.
    fn propagate_cf_deps(&mut self, is_loop: bool) -> Result<(), VisitorError> {
        let curr_cf_varset = &mut self.current_properties.control_flow_vars;
        if is_loop {
            if let Some(ref loop_cf) = self.loop_cf_conditions.take() {
                curr_cf_varset.merge_with_other(loop_cf);
            }
        }

        if curr_cf_varset.is_empty() {
            return Ok(());
        }
        if !is_loop {
            if let Some(ref mut cf_conditions) = self.loop_cf_conditions {
                cf_conditions.merge_with_other(curr_cf_varset);
            }
        }

        if self
            .current_properties
            .cf_flags
            .contains(ControlFlags::RETURN)
        {
            get_cur_fn_props!(self, get_mut)?
                .fn_ret_cf_conditions
                .merge_with_other(curr_cf_varset);
        }

        Ok(())
    }
    /// Marks, for the current statement properties, that it contains an AccessIndex expression.
    ///
    /// # Returns
    /// Whether the current properties changed because of this call.
    fn mark_access_indices_many(
        &mut self,
        exprs: &[Handle<Expression>],
    ) -> Result<(), VisitorError> {
        if self.current_properties.has_expr_access || exprs.is_empty() {
            return Ok(());
        }

        let exprs_with_accesses = &get_cur_fn_props!(self, get)?.exprs_with_accesses;
        for item in exprs {
            if exprs_with_accesses.contains(item) {
                self.current_properties.has_expr_access = true;
                break;
            }
        }
        Ok(())
    }

    fn mark_access_indices(&mut self, expr: Handle<Expression>) -> Result<(), VisitorError> {
        if self.current_properties.has_expr_access {
            return Ok(());
        }

        self.current_properties.has_expr_access = get_cur_fn_props!(self, get)?
            .exprs_with_accesses
            .contains(&expr);
        Ok(())
    }
}

impl std::ops::Index<Handle<crate::Function>> for ModuleStatementBuilder<'_> {
    type Output = FunctionProperties;

    fn index(&self, index: Handle<crate::Function>) -> &Self::Output {
        &self.fn_reads[&index]
    }
}

impl crate::TypeInner {
    /// Return whether the type can be indexed. This works as [`indexable_length`],
    /// except returns `false` where [`indexable_length`] would return `Err` and `true` where it would return an `Ok`.
    ///
    /// [`TypeInner::Struct`] is not considered indexable.
    ///
    /// [`indexable_length`]: crate::TypeInner::indexable_length
    /// [`TypeInner::Struct`]: crate::TypeInner::Struct
    fn is_indexable(&self, module: &crate::Module, config: AddressSpacesToCheck) -> bool {
        use crate::TypeInner as Ti;
        match *self {
            Ti::Vector { .. }
            | Ti::Matrix { .. }
            | Ti::Array { .. }
            | Ti::ValuePointer { size: Some(_), .. } => true,
            Ti::Pointer { base, space } if config.contains_address_space(space) => {
                // When assigning types to expressions, ResolveContext::Resolve
                // does a separate sub-match here instead of a full recursion,
                // so we'll do the same.
                let base_inner = &module.types[base].inner;
                match *base_inner {
                    Ti::Vector { .. } | Ti::Matrix { .. } | Ti::Array { .. } => true,
                    _ => false,
                }
            }
            _ => false,
        }
    }
}

impl<'module> ModuleStatementBuilder<'module> {
    /// Return the current expression arena based on `self.current_path`'s first element.
    ///
    /// # Panics
    /// Panics if the first element of `self.current_path` is not a function or entry point.
    fn get_current_expr_arena(&self) -> Result<&'module Arena<Expression>, VisitorError> {
        match self.current_path.first() {
            Some(&StatementPathPart::EntryPoint(EntryPointIndex(e))) => {
                Ok(&self.module.entry_points[e].function.expressions)
            }
            Some(&StatementPathPart::Function(f)) => Ok(&self.module.functions[f].expressions),
            _ => unreachable!("First element of current path is not a function or entry point."),
        }
    }

    /// Determine the read set for the expression, and update the current properties with it.
    /// Depending on `scope`, this updates either the control flow read set or the store read set.
    ///
    /// We also need to update the read set with self....
    ///
    /// # Panics
    ///
    /// We expect the entry point to be in the active path. If it is not, this function will panic.
    ///
    /// # Errors
    /// [`VisitorError::BadHandle`] if the payload for `expr` cannot be borrowed from the current function's subexpression map.
    fn update_with_read_set(
        &mut self,
        expr: Handle<Expression>,
        scope: ScopeKind,
    ) -> Result<(), VisitorError> {
        // Get the active fn
        let (fn_exprs, fn_props) = match self.current_path.first() {
            Some(&StatementPathPart::Function(h)) => (
                &self.module.functions[h].expressions,
                self.fn_reads
                    .get_mut(&h)
                    .unwrap_or_else(|| unreachable!("Expected function in active path")),
            ),
            Some(&StatementPathPart::EntryPoint(ref ep @ EntryPointIndex(i))) => (
                &self.module.entry_points[i].function.expressions,
                self.ep_reads
                    .get_mut(ep)
                    .unwrap_or_else(|| unreachable!("Expected entry point in active path")),
            ),
            _ => unreachable!("Expected function or entry point in active path"),
        };

        let active_fn_subexpr_map = &fn_props.subexpr_map;
        // SAFETY:
        // The unsafe here is needed for try_borrow_unguarded, for which we must guarantee
        // that the term we are borrowing from is not later borrowed mutably before our reference is dropped.
        // Here, the reference is dropped at the end of the function. We do no other borrows from any map in `active_fn_subexpr_map`,
        // and thus we have upheld the safety contract.
        let reads = unsafe {
            active_fn_subexpr_map
                .get(&expr)
                .unwrap_or_else(|| unreachable!("Expected function in active sub expression"))
                .try_borrow_unguarded()
                .map_err(|_| VisitorError::bad_handle(expr))?
        };

        let resolved_expr = &fn_exprs[expr];
        let self_as_tracked: Option<TrackedVar> = resolved_expr.try_into().ok();

        // Update the var set based on which scope we are provided.
        // Control flow is used for control flow in the statement.
        // StoreRead is used for store reads within the statement.
        // RetRead is used for variables that influence the return value.
        let var_set = match scope {
            ScopeKind::ControlFlow => &mut self.current_properties.control_flow_vars,
            ScopeKind::StoreRead => &mut self.current_properties.store_reads,
            // If this is a RetRead, then we just extend the retval dependencies with the read set.
            ScopeKind::RetRead => {
                fn_props.retval_dependencies.extend(reads);
                // If this expression is itself a local variable...
                if let Some(r) = self_as_tracked {
                    fn_props.retval_dependencies.insert(r);
                }
                return Ok(());
            }
        };

        for &read in reads.iter().chain(self_as_tracked.as_ref().into_iter()) {
            if let TrackedVar::CallResult(call_expr) = read {
                if let Expression::CallResult(called_fn_handle) = fn_exprs[call_expr] {
                    var_set.insert(called_fn_handle);
                } else {
                    unreachable!("CallResult expression is not a CallResult");
                }
            }
            var_set.insert(read);
        }
        Ok(())
    }

    /// Constructs the function properties for the function / entry point.
    ///
    /// Calls VarVisitor's `visit_arena` to get the subexpression map.
    fn build_function_properties(&mut self) -> Result<(), VisitorError> {
        // Function used to filter whether an AccessIndex expression's index should be
        // treated as a buffer access that needs to be tracked.
        // Right here is where we would exclude certain kinds of buffers whose
        // accesses we don't care to check the bounds of.
        // E.g., if we want to turn off checking bounds for Uniforms, then that logic would go in this function.
        // Specifically, one would modify the `is_indexable` function
        let build_property_for_fn =
            |func: &crate::Function| -> Result<FunctionProperties, VisitorError> {
                let visitor_result = VarVisitor::visit_arena(
                    &func.expressions,
                    &func.local_variables,
                    &self.module.global_variables,
                    &self.module.global_expressions,
                    Box::new(|e: Handle<Expression>| {
                        self.module_info[e]
                            .inner_with(&self.module.types)
                            .is_indexable(self.module, self.address_space_config)
                    }),
                )?;
                Ok(FunctionProperties {
                    subexpr_map: visitor_result.subexpr_map,
                    exprs_with_accesses: visitor_result.exprs_with_accesses,
                    index_access_dependencies: visitor_result.index_access_dependencies,
                    ..Default::default()
                })
            };

        // Go through the functions in the module
        for (fun_handle, fun) in self.module.functions.iter() {
            let new_fn_props = build_property_for_fn(fun)?;
            self.fn_reads.insert(fun_handle, new_fn_props);
        }

        // Now do the same for Entry points.
        for (ep_index, ep) in self.module.entry_points.iter().enumerate() {
            let new_ep_props = build_property_for_fn(&ep.function)?;
            self.ep_reads.insert(ep_index.into(), new_ep_props);
        }

        Ok(())
    }

    fn build(
        module: &'module crate::Module,
        module_info: &'module crate::valid::ModuleInfo,
        address_space_config: AddressSpacesToCheck,
    ) -> Result<Self, VisitorError> {
        // Begin the module builder.
        let mut builder = ModuleStatementBuilder {
            current_path: Vec::new(),
            statement_map: FastHashMap::default(),
            current_properties: StatementProperties::default(),
            module,
            module_info,
            ep_reads: FastHashMap::with_capacity_and_hasher(
                module.entry_points.len(),
                Default::default(),
            ),
            fn_reads: FastHashMap::with_capacity_and_hasher(
                module.functions.len(),
                Default::default(),
            ),
            marked_exprs: FastHashSet::default(),
            address_space_config,
            loop_cf_conditions: None,
        };

        builder.build_function_properties()?;

        // Go through each function.
        for (fun_handle, fun) in module.functions.iter() {
            // For each function, we need to compute the Variable reads. This is the first step.
            builder
                .current_path
                .push(StatementPathPart::Function(fun_handle));
            // Now, we visit the block in the body.
            builder.visit_Block(&fun.body)?;
            builder.loop_cf_conditions = None;
            // The current properties of the builder is the properties of the fn. We need to merge the fn props with this

            builder
                .fn_reads
                .get_mut(&fun_handle)
                .unwrap()
                .merge_from_statement_properties(&builder.current_properties);

            builder.current_path.pop();
        }
        // Now, go through each entry point.
        for (index, ep) in module.entry_points.iter().enumerate() {
            builder
                .current_path
                .push(StatementPathPart::EntryPoint(index.into()));
            builder.visit_Block(&ep.function.body)?;
            builder.current_path.pop();
        }

        Ok(builder)
    }
}

/// The kind of store to a pointer.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum PointerBase {
    /// The store is to a local variable with this handle
    LocalVariable(Handle<LocalVariable>),
    /// The store is to a global variable with this handle.
    GlobalVariable(Handle<GlobalVariable>),
    /// The store is to a function argument with this index.
    FunctionArgument(u32),
}

/// Wrapper used by [`VarVisitor`] that denotes the kind of read.
///
/// [`VarVisitor`]: self::VarVisitor
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum TrackedVar {
    LocalVariable(Handle<LocalVariable>),
    GlobalVariable(Handle<GlobalVariable>),
    FunctionArgument(u32),
    /// CallResult expressions that are used.
    /// The expression behind this handle should always be a `CallResult`.
    CallResult(Handle<Expression>),
}

impl TrackedVar {
    /// Turns the `TrackedVar` into a `MarkedExprKey`, with the key from the provided path.
    /// The provided path MUST be a function or entry point.
    ///
    /// # Panics
    /// Panics if the path is not a function or entry point.
    fn into_marked_expr_key_with(self, path: &StatementPathPart) -> MarkedExprKey {
        match self {
            TrackedVar::LocalVariable(l) => l.as_marked_key_with(path),
            TrackedVar::GlobalVariable(g) => MarkedExprKey::GlobalVariable(g),
            TrackedVar::FunctionArgument(a) => a.as_marked_key_with(path),
            TrackedVar::CallResult(c) => c.as_marked_key_with(path),
        }
    }
}

impl<T: AsRef<PointerBase>> From<T> for TrackedVar {
    fn from(base: T) -> Self {
        match *base.as_ref() {
            PointerBase::LocalVariable(l) => TrackedVar::LocalVariable(l),
            PointerBase::GlobalVariable(g) => TrackedVar::GlobalVariable(g),
            PointerBase::FunctionArgument(a) => TrackedVar::FunctionArgument(a),
        }
    }
}

impl From<PointerBase> for TrackedVar {
    fn from(base: PointerBase) -> Self {
        match base {
            PointerBase::LocalVariable(l) => TrackedVar::LocalVariable(l),
            PointerBase::GlobalVariable(g) => TrackedVar::GlobalVariable(g),
            PointerBase::FunctionArgument(a) => TrackedVar::FunctionArgument(a),
        }
    }
}

impl TryFrom<&Expression> for TrackedVar {
    type Error = &'static str;
    fn try_from(value: &Expression) -> Result<Self, Self::Error> {
        use crate::Expression as E;
        match *value {
            E::LocalVariable(l) => Ok(Self::LocalVariable(l)),
            E::GlobalVariable(g) => Ok(Self::GlobalVariable(g)),

            E::FunctionArgument(i) => Ok(Self::FunctionArgument(i)),
            _ => Err("Can't convert to tracked expression."),
        }
    }
}

impl crate::Function {
    /// Return the global variable, local variable, or function argument being accessed by `pointer`.
    ///
    /// Assuming that `pointer` is a series of `Access` and `AccessIndex`
    /// expressions that ultimately access some part of a [`GlobalVariable`], [`LocalVariable`], or [`FunctionArgument`],
    /// return a handle for that global.
    /// Similar to [`originating_global`], but instead returns a `PointerBase` enum that contains the kind of variable being accessed.
    ///
    /// # Panics
    /// Panics if `expr` does not ultimately access a `GlobalVariable`, `LocalVariable`, or `FunctionArgument`.
    ///
    /// [`GlobalVariable`]: crate::GlobalVariable
    /// [`LocalVariable`]: crate::LocalVariable
    /// [`FunctionArgument`]: crate::FunctionArgument
    /// [`originating_global`]: crate::Function::originating_global
    pub fn originating_var(&self, expr: Handle<Expression>) -> PointerBase {
        self.expressions.resolve_store_to_var(expr)
    }
}

impl Arena<Expression> {
    /// Resolve a store expression to the variable it writes to.
    ///
    /// # Panics
    /// Panics if the expression can't be used as a a pointer.
    fn resolve_store_to_var(&self, pointer: Handle<Expression>) -> PointerBase {
        let mut current = pointer;
        loop {
            match self[current] {
                Expression::LocalVariable(l) => {
                    return PointerBase::LocalVariable(l);
                }
                Expression::GlobalVariable(g) => {
                    return PointerBase::GlobalVariable(g);
                }
                Expression::FunctionArgument(a) => {
                    return PointerBase::FunctionArgument(a);
                }
                Expression::Access { base, .. } => {
                    current = base;
                }
                Expression::AccessIndex { base, .. } => {
                    current = base;
                }
                _ => unreachable!("Expression should not produce pointer value."),
            }
        }
    }
}

#[allow(non_snake_case)]
impl StatementVisitor<VisitorError> for ModuleStatementBuilder<'_> {
    /// Visit a statement, constructing the statement properties for it.
    ///
    // The basic idea is:
    // 1. Move `self.current_properties` into a temporary variable
    // 2. Set `self.current_properties` to a new, default `StatementProperties`
    // 3. Visit the statement (which will fill in the properties object)
    // 4. Write the now populated `self.current_properties` into the statement map for the current path
    // 5. Restore the old properties.
    fn visit_Statement(&mut self, statement: &Statement) -> Result<(), VisitorError> {
        // If the statement is a block, then bypass the default visitor and call the block visitor.
        // This is because the merge writes, etc. is also done by the block visitor.
        if let Statement::Block(ref block) = *statement {
            return self.visit_Block(block);
        }
        // Take the current properties, and then replace it with a new, empty properties object.
        let mut old_properties = std::mem::take(&mut self.current_properties);

        // Now, call the default statement visitor that dispatches to the correct visit method
        self.default_visit_Statement(statement)?;

        // Mark whether the statement is a terminator here.
        self.current_properties.is_terminator = statement.is_terminator();

        // Afterwards, we will have computed the properties of this statement. Thus, we merge the statement's
        // properties into the old properties so that they can be tied together.
        old_properties.merge_with(&self.current_properties);

        // Then, we add the statement's properties to the map, and restore `self.current_properties`
        self.statement_map.insert(
            self.current_path.clone(),
            std::mem::replace(&mut self.current_properties, old_properties),
        );

        Ok(())
    }

    /// Visits each statement in the block, constructs the statement properties for each, and
    /// then merges them with the current properties.
    fn visit_Block(&mut self, block: &Block) -> Result<(), VisitorError> {
        let mut old_properties = std::mem::take(&mut self.current_properties);
        // For blocks, I don't care about anything other than the variables they write to, and the control flow they have.
        // If we see a return, break, or continue, then we stop processing the rest of the elements.
        for (index, statement) in block.iter().enumerate() {
            self.current_path.push(StatementPathPart::Index(index));
            self.visit_Statement(statement)?;
            // Unwrap unsafe is OK here, since visit_Statement ALWAYS sets the current properties if its result was `Ok`
            let last_was_terminator = unsafe {
                self.statement_map
                    .get(&self.current_path)
                    .unwrap_unchecked()
            }
            .is_terminator;
            self.current_path.pop();
            // If the statement was a terminator, then so is this block, and we don't need to process any more statements in the block
            if last_was_terminator {
                self.current_properties.is_terminator = true;
                break;
            }
        }

        old_properties.merge_with(&self.current_properties);
        self.statement_map.insert(
            self.current_path.clone(),
            std::mem::replace(&mut self.current_properties, old_properties),
        );
        Ok(())
    }

    fn visit_Store(
        &mut self,
        pointer: Handle<Expression>,
        value: Handle<Expression>,
    ) -> Result<(), VisitorError> {
        let function = match self.current_path.first() {
            Some(&StatementPathPart::Function(fun_handle)) => &self.module.functions[fun_handle],
            Some(&StatementPathPart::EntryPoint(ep_index)) => {
                &self.module.entry_points[usize::from(ep_index)].function
            }
            _ => unreachable!("Store statement not in function or entry point."),
        };

        // Descend through the pointer chain, marking expressions used as indices as dependencies to a store.
        // When the store culminates in a variable, we mark that variable as the one written to.
        let mut current = pointer;
        loop {
            match function.expressions[current] {
                Expression::LocalVariable(l) => {
                    self.current_properties.lcl_writes.insert(l);
                    break;
                }
                Expression::GlobalVariable(g) => {
                    self.current_properties.glbl_writes.insert(g);
                }
                Expression::FunctionArgument(a) => {
                    self.current_properties.arg_writes.insert(a);
                }
                Expression::Access { base, index } => {
                    self.update_with_read_set(index, ScopeKind::StoreRead)?;
                    current = base;
                }
                Expression::AccessIndex { base, .. } => {
                    current = base;
                }
                _ => unreachable!("Expression should not produce pointer value."),
            }
        }

        // Visit the value expression, marking it as a dependency for the store.
        self.update_with_read_set(value, ScopeKind::StoreRead)?;
        Ok(())
    }

    fn visit_If(
        &mut self,
        condition: Handle<Expression>,
        accept: &Block,
        reject: &Block,
    ) -> Result<(), VisitorError> {
        self.update_with_read_set(condition, ScopeKind::ControlFlow)?;

        self.current_path.push(StatementPathPart::Accept);
        self.visit_Block(accept)?;
        let accept_is_terminator = self
            .statement_map
            .get(&self.current_path)
            .unwrap()
            .is_terminator;
        self.current_path.pop();

        self.current_path.push(StatementPathPart::Reject);
        self.visit_Block(reject)?;
        let reject_is_terminator = self
            .statement_map
            .get(&self.current_path)
            .unwrap()
            .is_terminator;
        self.current_path.pop();

        // If both the accept and reject blocks are terminators, then this if statement is a terminator, as both branches
        // unconditionally terminate.
        if accept_is_terminator && reject_is_terminator {
            self.current_properties.is_terminator = true;
        }

        let curr_cf_varset = &self.current_properties.control_flow_vars;
        // If we have any control flow vars here, we propagate them up..

        // We need to propagate the control flow dependencies up.
        self.propagate_cf_deps(false)
    }

    fn visit_Switch(
        &mut self,
        selector: Handle<Expression>,
        cases: &Vec<SwitchCase>,
    ) -> Result<(), VisitorError> {
        self.mark_access_indices(selector);

        for (index, case) in cases.iter().enumerate() {
            self.current_path.push(StatementPathPart::Case(index));
            self.visit_Block(&case.body)?;
            self.current_path.pop();
            // We don't care about `selector`, as it is only ever a Constant or a literal.
        }
        self.update_with_read_set(selector, ScopeKind::ControlFlow)?;
        self.propagate_cf_deps(false)
    }

    fn visit_Loop(
        &mut self,
        body: &Block,
        continuing: &Block,
        break_if: Option<Handle<Expression>>,
    ) -> Result<(), VisitorError> {
        self.current_path.push(StatementPathPart::LoopBody(0));
        self.visit_Block(body)?;
        self.current_path.pop();

        self.current_path.push(StatementPathPart::LoopContinuing(0));
        self.visit_Block(continuing)?;
        self.current_path.pop();

        // After visiting the `body` and the `continuing`, we update the control flow dependencies for the loop.
        // That is, in addition to the `break_if` and
        if let Some(break_if) = break_if {
            self.update_with_read_set(break_if, ScopeKind::ControlFlow)?;
        }

        self.propagate_cf_deps(true)?;

        // We might have set these based on the block that contain us. We reset them here.
        self.current_properties.is_terminator = false;
        // a `loop` statement cannot contain any break or continue statements at all, though it might
        self.current_properties.cf_flags &= !(ControlFlags::BREAK | ControlFlags::CONTINUE);
        Ok(())
    }

    /// Visiting a return statement marks any values in the return expression as dependencies for the function's `return` value.
    fn visit_Return(&mut self, value: Option<Handle<Expression>>) -> Result<(), VisitorError> {
        self.current_properties.cf_flags |= ControlFlags::RETURN;
        if let Some(value) = value {
            self.update_with_read_set(value, ScopeKind::RetRead)?;
        }
        // We also need to propagate the control flow dependencies up to the body of the fn.
        // That way, we know exactly what variables will halt the control flow of the function.
        Ok(())
    }

    fn visit_Atomic(
        &mut self,
        pointer: Handle<Expression>,
        fun: crate::AtomicFunction,
        value: Handle<Expression>,
        result: Option<Handle<Expression>>,
    ) -> Result<(), VisitorError> {
        if let Some(e) = result {
            self.mark_access_indices_many(&[pointer, value, e])
        } else {
            self.mark_access_indices_many(&[pointer, value])
        }?;

        // The `pointer` behind the atomic is ultimately written to
        match self.get_current_expr_arena()?[pointer] {
            Expression::LocalVariable(l) => self.current_properties.lcl_writes.insert(l),
            Expression::GlobalVariable(g) => self.current_properties.glbl_writes.insert(g),
            Expression::FunctionArgument(a) => self.current_properties.arg_writes.insert(a),
            _ => true,
        };
        Ok(())
    }

    fn visit_ImageStore(
        &mut self,
        image: Handle<Expression>,
        coordinate: Handle<Expression>,
        array_index: Option<Handle<Expression>>,
        value: Handle<Expression>,
    ) -> Result<(), VisitorError> {
        if let Some(array_index) = array_index {
            self.mark_access_indices_many(&[image, coordinate, value, array_index])
        } else {
            self.mark_access_indices_many(&[image, coordinate, value])
        }
    }

    /// Visits a call statement.
    ///
    /// If any of the arguments contain access indices, then this expression is marked as having access indices.
    /// If any of the arguments are written to by the called function, then they are marked as written by this statement.
    fn visit_Call(
        &mut self,
        function: Handle<crate::Function>,
        arguments: &[Handle<Expression>],
        result: Option<Handle<Expression>>,
    ) -> Result<(), VisitorError> {
        self.mark_access_indices_many(arguments);
        // Go through the function's indices.
        let fn_props = self.fn_reads.get(&function).unwrap(); // We want to panic if the function couldn't be found. This is a bug in the visitor.

        self.current_properties.has_expr_access |= fn_props.has_access_indices;
        self.current_properties.has_call = true;

        let current_arena = self.get_current_expr_arena()?;
        for arg in &fn_props.arg_writes {
            match current_arena[arguments[*arg as usize]] {
                Expression::GlobalVariable(g) => self.current_properties.glbl_writes.insert(g),
                Expression::LocalVariable(l) => self.current_properties.lcl_writes.insert(l),
                Expression::FunctionArgument(arg) => self.current_properties.arg_writes.insert(arg),
                _ => true,
            };
        }

        if let Some(e) = result {
            // get the handle
            let Expression::CallResult(other_fn_handle) = current_arena[e] else {
                unreachable!();
            };
            let my_props = get_cur_fn_props!(self, get)?;
            // Get the fn props of `other`.
            let other_props = self.fn_reads.get(&other_fn_handle).unwrap(); // If the other couldn't be found, we have a bug in the visitor. We want to panic.

            // Have to get my arguments as mut
            let mut this_expr = my_props
                .subexpr_map
                .get(&e)
                .unwrap()
                .try_borrow_mut()
                .map_err(|_| VisitorError::bad_handle(e))?;

            // Now, for every arg that influences retval, mark it.
            for arg in &other_props.retval_dependencies {
                match *arg {
                    gvar @ TrackedVar::GlobalVariable(_) => this_expr.insert(gvar),
                    TrackedVar::FunctionArgument(a) => match current_arena[arguments[a as usize]] {
                        Expression::GlobalVariable(g) => {
                            this_expr.insert(TrackedVar::GlobalVariable(g))
                        }
                        Expression::LocalVariable(l) => {
                            this_expr.insert(TrackedVar::LocalVariable(l))
                        }

                        Expression::FunctionArgument(a) => {
                            this_expr.insert(TrackedVar::FunctionArgument(a))
                        }
                        _ => true,
                    },
                    _ => true,
                };
            }
        }
        self.current_properties.is_terminator = false;
        Ok(())
    }

    fn visit_Break(&mut self) -> Result<(), VisitorError> {
        if self.loop_cf_conditions.is_none() {
            self.loop_cf_conditions = Some(VarSet::default());
        }
        self.current_properties.cf_flags |= ControlFlags::BREAK;
        Ok(())
    }

    /// Visting continue causes `self.loop_cf_conditions` to become a `VarSet` if it is not already.
    fn visit_Continue(&mut self) -> Result<(), VisitorError> {
        // If we see a continue, then we stop iterating future items in the block.
        if self.loop_cf_conditions.is_none() {
            self.loop_cf_conditions = Some(VarSet::default());
        }
        self.current_properties.cf_flags |= ControlFlags::CONTINUE;
        Ok(())
    }

    fn visit_Kill(&mut self) -> Result<(), VisitorError> {
        self.current_properties.is_terminator = true;
        self.current_properties.cf_flags |= ControlFlags::KILL;
        Ok(())
    }

    fn visit_RayQuery(
        &mut self,
        query: Handle<Expression>,
        fun: &crate::RayQueryFunction,
    ) -> Result<(), VisitorError> {
        self.mark_access_indices(query);
        Ok(())
    }

    fn visit_SubgroupCollectiveOperation(
        &mut self,
        op: crate::SubgroupOperation,
        collective_op: crate::CollectiveOperation,
        argument: Handle<Expression>,
        result: Handle<Expression>,
    ) -> Result<(), VisitorError> {
        self.mark_access_indices(argument)
    }
    fn visit_WorkGroupUniformLoad(
        &mut self,
        pointer: Handle<Expression>,
        result: Handle<Expression>,
    ) -> Result<(), VisitorError> {
        self.mark_access_indices(pointer)
    }

    fn visit_SubgroupGather(
        &mut self,
        mode: crate::GatherMode,
        argument: Handle<Expression>,
        result: Handle<Expression>,
    ) -> Result<(), VisitorError> {
        self.mark_access_indices(argument)
    }

    fn visit_SubgroupBallot(
        &mut self,
        result: Handle<Expression>,
        predicate: Option<Handle<Expression>>,
    ) -> Result<(), VisitorError> {
        if let Some(p) = predicate {
            self.mark_access_indices(p)
        } else {
            Ok(())
        }
    }
}

/// This struct is used to drive step 3 of the visitor.
///
///
/// In step 3, we mark all [`TrackedVar`]s that must be tracked for bounds checking. This is done by continually looping through each function's arena, and marking an expression if it
/// - Is used to compute an access index
/// - Is a dependency of a store statement to a `TrackedVar` that has been marked
/// - Is a dependency of a control flow statement that contains an access index or a store to a marked expression.
/// - It is an argument to a function call where either
///    - The function call's associated FunctionArgument is marked
///    - The function call's associated CallResult is marked and the corresponding function's FunctionArgument is a dependency of `RetVal`
/// [`TrackedVar`]: self::TrackedVar
struct ModuleStatementBuilderPhase2<'module> {
    current_path: Vec<StatementPathPart>,
    statement_map: FastHashMap<Vec<StatementPathPart>, StatementProperties>,
    module: &'module crate::Module,
    module_info: &'module crate::valid::ModuleInfo,
    address_space_config: AddressSpacesToCheck,
    loop_cf_conditions: Option<VarSet>,
    ep_reads: FastHashMap<EntryPointIndex, FunctionProperties>,
    fn_reads: FastHashMap<Handle<crate::Function>, FunctionProperties>,
    marked_any: bool,
    /// Whether a statement within was marked.
    did_mark_statement: bool,
    /// Tracks different things that may need to be visited.
    marked_exprs: FastHashSet<MarkedExprKey>,
}

impl<'module> From<ModuleStatementBuilder<'module>> for ModuleStatementBuilderPhase2<'module> {
    fn from(builder: ModuleStatementBuilder<'module>) -> Self {
        Self {
            current_path: Vec::new(),
            statement_map: builder.statement_map,
            module: builder.module,
            module_info: builder.module_info,
            address_space_config: builder.address_space_config,
            loop_cf_conditions: builder.loop_cf_conditions,
            ep_reads: builder.ep_reads,
            fn_reads: builder.fn_reads,
            marked_any: false,
            marked_exprs: FastHashSet::default(),
            did_mark_statement: false,
        }
    }
}

impl std::ops::Index<EntryPointIndex> for crate::Module {
    type Output = EntryPoint;
    /// Return the function for the entry point at the given index.
    #[inline]
    fn index(&self, index: EntryPointIndex) -> &Self::Output {
        let EntryPointIndex(index) = index;
        &self.entry_points[index]
    }
}

impl std::ops::Index<Handle<crate::Function>> for crate::Module {
    type Output = crate::Function;

    /// Return the function for the given handle.
    #[inline]
    fn index(&self, index: Handle<crate::Function>) -> &Self::Output {
        &self.functions[index]
    }
}

impl ModuleStatementBuilderPhase2<'_> {
    fn get_current_expr_arena(&self) -> Result<&Arena<Expression>, VisitorError> {
        let path = self.current_path.first().unwrap_or_else(|| {
            unreachable!("Expect first element of path to be function or entry point.")
        });
        match *path {
            StatementPathPart::Function(fun_handle) => {
                Ok(&self.module.functions[fun_handle].expressions)
            }
            StatementPathPart::EntryPoint(ep_index) => Ok(&self.module.entry_points
                [usize::from(ep_index)]
            .function
            .expressions),
            _ => unreachable!("Expect first element of path to be function or entry point."),
        }
    }

    // A statement must be visited if it...
    // - Writes to a marked variable
    // - Contains an access index.
    // - Contains any control flow that carries over outside of the statement iself, when the statement it carries to
    // contains either of the above.
    // All other statements can be safely ignored. This allows us to skip over statements that don't matter.

    fn build(phase1: ModuleStatementBuilder<'_>) -> Result<(), VisitorError> {
        macro_rules! mark_fn_body {
            (@step1 $(,)? $builder:ident, $fn_iter_expr:expr, $fn_iter:expr, $arg_variant:expr, $call_variant:expr, $local_variant:expr, $statement_path_expr:expr $(,)?) => {
                // Part 1. Mark all expressions used as access indices.
                for (prop_key, props) in $fn_iter_expr {
                    $builder.marked_any |= !props.index_access_dependencies.is_empty();
                    for expr in &props.index_access_dependencies {
                        $builder.marked_any |= match *expr {
                            TrackedVar::FunctionArgument(a) => {
                                $builder.marked_exprs.insert($arg_variant(*prop_key, a))
                            }
                            TrackedVar::GlobalVariable(g) => $builder
                                .marked_exprs
                                .insert(MarkedExprKey::GlobalVariable(g)),

                            TrackedVar::LocalVariable(l) => {
                                $builder.marked_exprs.insert($local_variant(*prop_key, l))
                            }
                            TrackedVar::CallResult(r) => {
                                $builder.marked_exprs.insert($call_variant(*prop_key, r))
                            }
                        };
                    }
                }
            };
            (@step2 $(,)? $builder:ident $(,)? $fn_iter_expr:expr, $fn_iter:expr, $arg_variant:expr, $call_variant:expr, $local_variant:expr, $statement_path_expr:expr $(,)?) => {
                for (fun_key, fun) in $fn_iter {
                    // This just visits the block of the function body.
                    $builder.current_path.push($statement_path_expr(fun_key));
                    $builder.visit_Block(&fun.body)?;
                    $builder.current_path.pop();
                }
            };
            (@entrypoint $(,)? @$stepid:ident $(,)? $builder:ident, $module:ident $(,)?) => {
                mark_fn_body! {
                    @$stepid,
                    $builder,
                    $builder.ep_reads.iter(),
                    $module.entry_points.iter().enumerate().map(|(i, e)| (EntryPointIndex(i), &e.function)),
                    MarkedExprKey::EntryPointArgument,
                    MarkedExprKey::EpCallResult,
                    MarkedExprKey::EntryPointLocal,
                    StatementPathPart::EntryPoint,
                };
            };
            (@function $(,)? @$stepid:ident $(,)? $builder:ident, $module:ident $(,)?) => {
                mark_fn_body! {
                    @$stepid
                    $builder,
                    $builder.fn_reads.iter(),
                    $module.functions.iter(),
                    MarkedExprKey::FunctionArgument,
                    MarkedExprKey::FnCallResult,
                    MarkedExprKey::FunctionLocal,
                    StatementPathPart::Function,
                };
            };
        };
        // First pass, mark all vars that are used as access indices. This is static, so we only do this once.
        let module = phase1.module;
        let mut builder = ModuleStatementBuilderPhase2::from(phase1);
        mark_fn_body! {@entrypoint @step1 builder, module};
        mark_fn_body! {@function @step1 builder, module};

        while (builder.marked_any) {
            builder.marked_any = false;

            mark_fn_body! {@entrypoint @step2, builder, module};
            mark_fn_body! {@function @step2, builder, module};
        }

        Ok(())
    }

    fn get_current_statement_props(&self) -> Option<&StatementProperties> {
        self.statement_map.get(&self.current_path)
    }

    fn get_current_statement_props_mut(&mut self) -> Option<&mut StatementProperties> {
        self.statement_map.get_mut(&self.current_path)
    }
}

impl VarSet {
    /// Converts these variables into tracked vars from the given `path`, and inserts them into the provided set.
    fn mark_all(&self, path: StatementPathPart, set: &mut FastHashSet<MarkedExprKey>) -> bool {
        let mut any_marked = false;
        for var in &self.gvars {
            any_marked |= set.insert(MarkedExprKey::GlobalVariable(*var));
        }
        for var in &self.lvars {
            any_marked |= set.insert(var.as_marked_key_with(&path));
        }
        for var in &self.function_args {
            any_marked |= set.insert(var.as_marked_key_with(&path));
        }

        for var in &self.function_calls {
            any_marked |= set.insert(MarkedExprKey::Function(*var));
        }

        for var in &self.call_results {
            any_marked |= set.insert(var.as_marked_key_with(&path));
        }

        any_marked
    }
}

/// This visitor implementation drives portions 2 and 3 of step 2.
/// At this point, all expressions that are used as access indices have been marked.
/// What this does is marks all expressions that are dependencies of a store to a marked expression,
/// and all expressions that are dependencies of a control flow statement that contains a marked statement.
///
/// In step 3, we mark all [`TrackedVar`]s that must be tracked for bounds checking. This is done by continually looping through each function's arena, and marking an expression if it
/// - Is used to compute an access index
/// - Is a dependency of a store statement to a `TrackedVar` that has been marked
/// - Is a dependency of a control flow statement that contains an access index or a store to a marked expression.
/// - It is an argument to a function call where either
///    - The function call's associated FunctionArgument is marked
///    - The function call's associated CallResult is marked and the corresponding function's FunctionArgument is a dependency of `RetVal`
/// [`TrackedVar`]: self::TrackedVar
///
/// While we visit every statement, we only override the default visitor
/// for statements that contain other statements.
///
/// This is because we can mark statements based on the properties they already computed.

impl<'module> StatementVisitor<VisitorError> for ModuleStatementBuilderPhase2<'module> {
    // Mark all stores to marked variables.
    fn visit_Store(
        &mut self,
        pointer: Handle<Expression>,
        value: Handle<Expression>,
    ) -> Result<(), VisitorError> {
        let current_path = &self.current_path[0];
        // Get the props for this statement.
        // We already computed the local, global, or arg we stored to, so just use it here.
        let props = self.statement_map.get(&self.current_path).unwrap();
        if props.lcl_writes.iter().any(|&lcl| {
            self.marked_exprs
                .contains(&lcl.as_marked_key_with(current_path))
        }) || props.glbl_writes.iter().any(|&glbl| {
            self.marked_exprs
                .contains(&glbl.as_marked_key_with(current_path))
        }) || props.arg_writes.iter().any(|&arg| {
            self.marked_exprs
                .contains(&arg.as_marked_key_with(current_path))
        }) {
            self.marked_any |= props
                .store_reads
                .mark_all(self.current_path[0], &mut self.marked_exprs);
        }

        Ok(())
    }
    /// Before calling default_visit, we mark the statement if we know that it contains a store to a marked expression.
    ///
    /// # Panics
    /// Panics if the current statement does not exist in the property map.
    fn visit_Statement(&mut self, statement: &Statement) -> Result<(), VisitorError> {
        // let props = self.statement_map.get_mut(&self.current_path).unwrap();
        // Only visit a statement if it might need to be visited.

        let (may_need_visit, is_marked) = {
            let tmp = self.statement_map.get(&self.current_path).unwrap();
            (tmp.may_need_visit(), tmp.marked)
        };

        if may_need_visit && !is_marked {
            // Visit the statement.
            let curr_path = &self.current_path[0];

            let props = self.statement_map.get_mut(&self.current_path).unwrap();

            props.marked = props.marked
                // Case 1: We have an expression access
                || props.has_expr_access
                // Case 2: We have a return statement, and this function either has access indices,
                // a store to a marked variable, or 
                || (props.has_ret()
                    && get_cur_fn_props!(self, get)?.has_access_indices
                    && matches!(self.current_path[0], StatementPathPart::Function(handle) if self.marked_exprs.contains(&MarkedExprKey::Function(handle))))
                || props.arg_writes.iter().any(|&arg| {
                    self.marked_exprs
                        .contains(&arg.as_marked_key_with(curr_path))
                })
                || props.lcl_writes.iter().any(|&lcl| {
                    self.marked_exprs
                        .contains(&lcl.as_marked_key_with(curr_path))
                })
                || props.glbl_writes.iter().any(|&glbl| {
                    self.marked_exprs
                        .contains(&glbl.as_marked_key_with(curr_path))
                });

            // If it was not marked before
            self.marked_any |= props.marked;
        }

        if may_need_visit {
            self.default_visit_Statement(statement)
        } else {
            Ok(())
        }
    }

    fn visit_Block(&mut self, block: &Block) -> Result<(), VisitorError> {
        // Only visit a block if it might need to be visited.
        let props = self.get_current_statement_props().unwrap();
        if props.may_need_visit() {
            for (index, statement) in block.iter().enumerate() {
                self.current_path.push(StatementPathPart::Index(index));
                self.visit_Statement(statement)?;

                let last_was_terminator = self
                    .statement_map
                    .get(&self.current_path)
                    .unwrap()
                    .is_terminator;
                self.current_path.pop();
                if last_was_terminator {
                    break;
                }
            }
        }
        Ok(())
    }

    fn visit_If(
        &mut self,
        condition: Handle<Expression>,
        accept: &Block,
        reject: &Block,
    ) -> Result<(), VisitorError> {
        self.current_path.push(StatementPathPart::Accept);
        self.visit_Block(accept);
        self.current_path.pop();

        self.current_path.push(StatementPathPart::Reject);
        self.visit_Block(reject);
        self.current_path.pop();

        let props = self.statement_map.get_mut(&self.current_path).unwrap();
        props
            .control_flow_vars
            .mark_all(self.current_path[0], &mut self.marked_exprs);

        Ok(())
    }

    fn visit_Call(
        &mut self,
        function: Handle<crate::Function>,
        arguments: &[Handle<Expression>],
        result: Option<Handle<Expression>>,
    ) -> Result<(), VisitorError> {
        // Determine if the call needs to be visited.
        // It needs to be visited if:
        // 1. It contains an access index
        //  In this case, we mark all of our arguments that flow into the call.
        // 2. It contains an access index
        // 3.

        // Part 1: This contains an access index.
        // Get the properties for the function.
        // First step, mark all index access expressions that are dependencies of the call.
        let other_fn_props = self
            .fn_reads
            .get(&function)
            .ok_or(VisitorError::NotFound("Function"))?;

        if other_fn_props.is_marked {
            self.statement_map
                .get_mut(&self.current_path)
                .unwrap()
                .marked = true;
        }

        Ok(())
    }
}

mod tests {
    use super::*;
    use crate::front::wgsl::parse_str;
    use crate::valid::{Capabilities, ValidationFlags, Validator};

    // Now, let's start by parsing a simple wgsl file.
    // We can only run the test if the `wgsl-in` feature is enabled.
    #[test]
    #[cfg(feature = "wgsl-in")]
    fn simple_test() {
        let module = parse_str(
            r#"
            fn main() {
                var a : f32;
                a = 1.0;
            }
        "#,
        )
        .unwrap();

        let mut validator = Validator::new(ValidationFlags::all(), Capabilities::all());
        let validated = validator.validate(&module).unwrap();

        println!("VALIDATION SUCCESS!");

        // we validate the module to get a builder

        let mut builder =
            ModuleStatementBuilder::build(&module, &validated, AddressSpacesToCheck::all()).unwrap();
        
        // Now let's print out the statement map!
        for (path, props) in builder.statement_map.iter() {
            println!("Path: {:?}", path);
            println!("Properties: {:?}", props);
        }
    }
}
