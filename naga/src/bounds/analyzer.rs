// SPDX-FileCopyrightText: 2024 University of Rochester
//
// SPDX-License-Identifier: MIT

#![allow(
    dead_code,
    unused_variables,
    unused_imports,
    clippy::match_wildcard_for_single_variants
)]

///! This module contains the analyzer for computing the bounds information for all buffer accesses.
use super::visitor::{
    EntryPointIndex, ExpressionVisitor, IntoMarkedKey, ModuleVisitorInfo, StatementPathPart,
    StatementVisitor,
};
use super::{AddressSpacesToCheck, BoundsCheckError};

use super::utils::{expression_variant, statement_variant};

use std::borrow::BorrowMut;
use std::collections::hash_map::Entry;
use std::{
    any,
    collections::{HashMap, VecDeque},
    fmt::Debug,
    ops,
};

use super::helper_interface::{self, HasName, HasType};

use crate::bounds::visitor::MarkedExprKey;
use crate::proc::ExpressionKind;
use crate::LocalVariable;
use crate::{
    non_max_u32::NonMaxU32,
    valid::{GlobalUse, ModuleInfo},
    AddressSpace, ArraySize, FastHashMap, FastHashSet, FunctionArgument, GlobalVariable, Module,
    Statement,
};
use abc_helper::{
    self, AbcExpression, AbcScalar, AbcType, ConstraintInterface, Predicate, StructField, Term,
};

use log::{info as log_info, trace as log_trace};
use rustc_hash::{FxHashMap, FxHashSet};

/// Convenience struct used to pass around a module with its info together in one term.
#[derive(Clone, Copy)]
struct ModuleWithInfo<'a> {
    module: &'a Module,
    validation_info: &'a ModuleInfo,
}

#[derive(Debug, Clone, Copy)]
enum FnKey {
    Function(crate::Handle<crate::Function>),
    EntryPoint(EntryPointIndex),
}

impl From<FnKey> for StatementPathPart {
    fn from(key: FnKey) -> Self {
        match key {
            FnKey::Function(f) => StatementPathPart::Function(f),
            FnKey::EntryPoint(e) => StatementPathPart::EntryPoint(e),
        }
    }
}

/// Convenience struct used to pass around a function with its info together in one term.
#[derive(Debug, Clone)]
struct FunctionWithInfo<'a> {
    func: &'a crate::Function,
    info: &'a crate::valid::FunctionInfo,
    key: FnKey,
}

/// Type alias for the handle type used in the AbcHelper
type ConstraintHandle<T> = <abc_helper::ConstraintHelper as ConstraintInterface>::Handle<T>;

/// this struct is used for information that is passed amongst visitors.
struct VisitorInfo<'module> {
    current_path: std::cell::RefCell<Vec<StatementPathPart>>,
    module_info: ModuleWithInfo<'module>,
    block_ctx: BlockContext,
    func_ctx: FunctionWithInfo<'module>,
    func_summary: std::cell::RefCell<PartialFunctionSummary>,
}

macro_rules! get_cur_fn_props {
    ($self:ident, $get_method:ident) => {
        match $self.current_path.first() {
            Some(&StatementPathPart::EntryPoint(ref e)) => $self
                .visitor_info
                .ep_reads
                .$get_method(e)
                .expect("Entry point should exist"),
            Some(&StatementPathPart::Function(ref f)) => $self
                .visitor_info
                .fn_reads
                .$get_method(f)
                .expect("Function should exist"),
            _ => panic!("get_cur_fn_props! must only be passed an entry point or function handle path part.")
        }
    };
}

/// Macros to get references to things in the current context.
macro_rules! get_ref {
    (@mut @func_summary, $self:expr) => {
        $self
            .current_fn_summary
            .as_mut()
            .expect("Function summary should be populated before visiting expressions")
    };
    (@func_summary, $self:expr) => {
        $self
            .current_fn_summary
            .as_ref()
            .expect("Function summary should be populated before visiting expressions")
    };
    (@module_info, $self:expr) => {
        $self
            .module_info
            .as_ref()
            .expect("Module info should be populated before visiting expressions")
    };
    (@func_ctx, $self:expr) => {
        $self
            .current_fn_info
            .as_ref()
            .expect("Function info should be populated before visiting expressions")
    };
    (@block_ctx, $self:expr) => {
        $self
            .current_block_ctx
            .as_ref()
            .expect("Block context should be populated before visiting expressions")
    };
    (@mut @block_ctx, $self:expr) => {
        $self
            .current_block_ctx
            .as_mut()
            .expect("Block context should be populated before visiting expressions")
    };
}
/// The bounds checker acts acts as the Bridge between a [`Module`] and the Constraint Helper.
///
/// This struct can be referenced, similarly to [`ModuleInfo`], to get the bounds requirements for the functions in the module.
///
/// To populate the bounds information, call [`abc_impl`]
///
///
/// [`Module`]: crate::Module
/// [`ModuleInfo`]: crate::ModuleInfo
/// [`abc_impl`]: BoundsChecker::abc_impl
#[derive(Default)]
pub struct BoundsChecker<'module> {
    // Arena of vars we have...
    pub helper: abc_helper::ConstraintHelper,

    pub global_vars: Vec<Term>,
    // Global expressions for the main module...
    pub global_exprs: FastHashMap<crate::Handle<crate::Expression>, Term>,
    // Functions in the scope...
    pub functions: Vec<FunctionSummary>,

    /// Entry points are unique in that there is no handle to the contained function.
    /// They are always indexed by their position in the entry point vector.
    pub entry_points: Vec<FunctionSummary>,
    /// Used to get the expression representing an override
    pub overrides: Vec<Term>,
    /// Used to get the expression representing a constant
    pub constants: Vec<Term>,
    /// Contains the types in the module converted to the AbcType form. Indexed by the handle.
    pub types: Vec<ConstraintHandle<AbcType>>,

    // Counter for symbols to ensure they are in SSA form.
    pub unique_counter: FastHashMap<String, u32>,

    /// The current function info.
    current_fn_info: Option<FunctionWithInfo<'module>>,

    /// The current block context.
    current_block_ctx: Option<BlockContext>,

    /// The current function summary.
    current_fn_summary: Option<PartialFunctionSummary>,

    buffer_config: AddressSpacesToCheck,

    module_info: Option<ModuleWithInfo<'module>>,

    /// The current path of what we're visiting.
    current_path: Vec<StatementPathPart>,

    /// The visitor information obtained from running the visitor on the module.
    visitor_info: ModuleVisitorInfo,

    /// The address spaces we have been configured to be interested in checking.
    address_space_config: AddressSpacesToCheck,
}

impl BoundsChecker<'_> {
    pub fn new(address_space_config: AddressSpacesToCheck) -> Self {
        Self {
            address_space_config,
            ..Default::default()
        }
    }
    /// Gets the current path.

    /// Push a path part to the current path.
    ///
    /// # Panics
    /// Panics if `self.visitor_info` has been borrowed mutably.
    #[inline]
    fn push_path_part(&mut self, part: StatementPathPart) {
        self.current_path.push(part);
    }

    #[inline]
    fn pop_path_part(&mut self) -> Option<StatementPathPart> {
        self.current_path.pop()
    }
}

impl ops::Index<crate::Handle<crate::Type>> for BoundsChecker<'_> {
    type Output = ConstraintHandle<AbcType>;
    fn index(&self, handle: crate::Handle<crate::Type>) -> &Self::Output {
        &self.types[handle.index()]
    }
}

impl ops::Index<crate::Handle<GlobalVariable>> for BoundsChecker<'_> {
    type Output = Term;
    fn index(&self, handle: crate::Handle<GlobalVariable>) -> &Self::Output {
        &self.global_vars[handle.index()]
    }
}

impl ops::Index<crate::Handle<crate::Function>> for BoundsChecker<'_> {
    type Output = FunctionSummary;
    fn index(&self, handle: crate::Handle<crate::Function>) -> &Self::Output {
        &self.functions[handle.index()]
    }
}

impl ops::IndexMut<crate::Handle<crate::Function>> for BoundsChecker<'_> {
    fn index_mut(&mut self, handle: crate::Handle<crate::Function>) -> &mut FunctionSummary {
        &mut self.functions[handle.index()]
    }
}

impl ops::Index<crate::Handle<crate::Expression>> for BoundsChecker<'_> {
    type Output = Term;
    fn index(&self, handle: crate::Handle<crate::Expression>) -> &Self::Output {
        &self.global_exprs[&handle]
    }
}

impl ops::Index<crate::Handle<crate::Override>> for BoundsChecker<'_> {
    type Output = Term;
    fn index(&self, handle: crate::Handle<crate::Override>) -> &Self::Output {
        &self.overrides[handle.index()]
    }
}

impl ops::Index<crate::Handle<crate::Constant>> for BoundsChecker<'_> {
    type Output = Term;
    fn index(&self, handle: crate::Handle<crate::Constant>) -> &Self::Output {
        &self.constants[handle.index()]
    }
}

/// Container that holds the intermediate state of the function summary while it is being constructed.
///
/// Once the function has been parsed, [`abc_impl`] will turn this into a [`FunctionSummary`] by calling [`to_function_summary`].
///
/// [`abc_impl`]: BoundsChecker::abc_impl
/// [`to_function_summary`]: PartialFunctionSummary::to_function_summary
/// [`FunctionSummary`]: FunctionSummary
struct PartialFunctionSummary {
    // Map from expression handles in the function to Expressions in the helper.
    // Expressions are always assigned to variables, so this actually maps to the handle of that variable.
    expressions: FastHashMap<crate::Handle<crate::Expression>, Term>,
    arguments: Vec<Term>,
    local_variabes: Vec<Term>,
    ret_ty: ConstraintHandle<AbcType>,
    /// Whether this expression has already been checked for its indices.
    checked_exprs: FastHashSet<crate::Handle<crate::Expression>>,
    nargs: u8,
}

/// Partial function summary is a function summary without a handle. The handle is added at the end.
impl PartialFunctionSummary {
    fn into_function_summary(
        self,
        handle: ConstraintHandle<abc_helper::Summary>,
    ) -> FunctionSummary {
        FunctionSummary {
            expressions: self.expressions,
            arguments: self.arguments,
            local_variabes: self.local_variabes,
            handle,
            ret_ty: self.ret_ty,
        }
    }
}

impl ops::Index<crate::Handle<crate::Expression>> for PartialFunctionSummary {
    type Output = Term;
    /// PartialFunctionSummary can be indexed by an expression handle to get
    /// the helper's `Term` corresponding to the expression.
    fn index(&self, handle: crate::Handle<crate::Expression>) -> &Self::Output {
        &self.expressions[&handle]
    }
}

impl ops::Index<crate::Handle<LocalVariable>> for PartialFunctionSummary {
    type Output = Term;
    /// PartialFunctionSummary can be indexed by a local variable handle to get
    /// the helper's `Term` corresponding to the local variable.
    fn index(&self, handle: crate::Handle<LocalVariable>) -> &Self::Output {
        &self.local_variabes[handle.index()]
    }
}

/// A function summary.
///
/// A function summary works as a bridge between the function in the module and the `Summary` in the helper.
///
/// It can be indexed by an [`Expression`] handle to get the helper's last `Term` that corresponds to the expression.
/// It can also be indexed by a [`LocalVariable`] handle to get the helper's last `Term` corresponding to the local variable.
pub struct FunctionSummary {
    pub expressions: FastHashMap<crate::Handle<crate::Expression>, Term>,
    /// An arena containing the Terms that correspond to the arguments in the function.
    pub arguments: Vec<Term>,
    /// An arena containing the Terms that correspond to the local variables in the function.
    /// Indexed by the handle of the local variable.
    pub local_variabes: Vec<Term>,
    /// The handle to the function's summary in the helper.
    pub handle: ConstraintHandle<abc_helper::Summary>,
    pub ret_ty: ConstraintHandle<AbcType>,
}

impl ops::Index<crate::Handle<crate::Expression>> for FunctionSummary {
    type Output = Term;
    fn index(&self, handle: crate::Handle<crate::Expression>) -> &Self::Output {
        &self.expressions[&handle]
    }
}

impl ops::Index<crate::Handle<LocalVariable>> for FunctionSummary {
    type Output = Term;
    fn index(&self, handle: crate::Handle<LocalVariable>) -> &Self::Output {
        &self.local_variabes[handle.index()]
    }
}

#[derive(Debug, Clone)]
/// Either holds a u32 or a handle to an expression.
enum ExpressionOrLiteral {
    Expression(Term),
    Literal(u32),
}

impl std::fmt::Display for ExpressionOrLiteral {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match *self {
            ExpressionOrLiteral::Expression(ref e) => write!(f, "{}", e),
            ExpressionOrLiteral::Literal(l) => write!(f, "{}", l),
        }
    }
}

enum ResolvedAccess {
    Struct(crate::Type),
    Array {
        inner: crate::TypeInner,
        dimension: usize,
    },
}

enum TermModifyStatus {
    Modified,
    Unmodified,
    Forbidden,
}

#[derive(Debug, Clone)]
/// Maintains a map of the current symbols for local and global variables.
struct BlockContext {
    /// Holds local variables and whether or not they were modified in the context.
    pub(self) local_variable_map: FastHashMap<crate::Handle<LocalVariable>, (Term, bool)>,

    /// Holds global variables and whether or not they were modified in the context.
    pub(self) global_variable_map: FastHashMap<crate::Handle<GlobalVariable>, (Term, bool)>,
}

impl BlockContext {
    /// Return a new BlockContext with the modified flag of all variables reset.
    ///
    /// Meant to be used to track blocks that modified variables so we know
    /// how to update those variables.
    pub(self) fn reset_writes(&self) -> Self {
        let mut local_variable_map = self.local_variable_map.clone();
        for (_, &mut (_, ref mut modified)) in local_variable_map.iter_mut() {
            *modified = false;
        }
        let mut global_variable_map = self.global_variable_map.clone();
        for (_, &mut (_, ref mut modified)) in global_variable_map.iter_mut() {
            *modified = false;
        }
        BlockContext {
            local_variable_map,
            global_variable_map,
        }
    }
}

impl<'module> BoundsChecker<'module> {
    pub fn reset(&mut self) {
        self.functions.clear();
        self.global_vars.clear();
    }

    fn make_type(&mut self, ty: &crate::Type) -> Result<AbcType, BoundsCheckError> {
        use crate::TypeInner::*;
        // Wgsl doesn't allow self-referential types.
        // We also assume that any TypeInner in an arena refers to a type that is already defined in the arena.
        match ty.inner {
            // an atomic is just a scalar.
            Array { base, size, .. } => {
                let inner = self
                    .types
                    .get(base.index())
                    .ok_or(BoundsCheckError::UndefinedType)?;

                // Fastest way to build a string...
                match size {
                    ArraySize::Constant(s) => Ok(AbcType::SizedArray {
                        ty: inner.clone(),
                        size: s,
                    }),
                    ArraySize::Dynamic => Ok(AbcType::DynamicArray { ty: inner.clone() }),
                }
            }
            // Atomics and scalars are both scalars.
            Atomic(s) | Scalar(s) => Ok(AbcType::Scalar(AbcScalar::from(s))),
            Vector { size, scalar } => Ok(AbcType::SizedArray {
                ty: AbcType::Scalar(scalar.into()).into(),
                size: size.into(),
            }),
            Struct { ref members, .. } => {
                // We make a struct type
                let mut struct_fields = Vec::with_capacity(members.len());

                for member in members {
                    if member.binding.is_some() {
                        return Err(BoundsCheckError::Unsupported(
                            "Struct member with bindings".to_string(),
                        ));
                    }
                    let name = member.name.clone().ok_or(BoundsCheckError::Unsupported(
                        "Unnamed struct member".to_string(),
                    ))?;
                    struct_fields.push(StructField::new(
                        name,
                        self.types[member.ty.index()].clone(),
                    ));
                }
                Ok(AbcType::Struct {
                    members: struct_fields,
                })
            }
            _ => Err(BoundsCheckError::Unsupported(format!(
                "Unsupported type: {:?}",
                ty
            ))),
        }
    }

    /// Mark variables from an arena.
    ///
    /// `space` is used as an affix to the variable name in case this is an anonymous name.
    ///
    /// # Arguments
    /// * `handle` - The handle to the variable in the arena.
    /// * `term` - The variable itself.
    /// * `space` - The space to use as an affix to the variable name when it does not have one.
    fn mark_var<T: HasName + HasType>(
        &mut self,
        term: &T,
        space: &str,
    ) -> Result<Term, BoundsCheckError> {
        let varname = match *term.to_name() {
            Some(ref name) => {
                // Make the var
                self.next_var_name(name)
            }
            None => {
                let name = String::from("$anon_") + space;
                self.next_var_name(&name)
            }
        };
        let var = self
            .helper
            .declare_var(abc_helper::Var { name: varname })
            .map_err(BoundsCheckError::ConstraintHelperError)?;

        // Mark the type of the variable
        let ty = self.types[term.to_type().index()].clone();
        self.helper
            .mark_type(&var, &ty)
            .map_err(BoundsCheckError::ConstraintHelperError)?;

        Ok(var)
    }

    /// Get the next var name
    ///
    /// # Panics
    /// If the counter for the variable is greater than u32::Max
    #[allow(clippy::panic)]
    fn next_var_name(&mut self, name: &str) -> String {
        let counter = self.unique_counter.entry(name.to_string()).or_insert(0);
        if *counter == 0 {
            *counter += 1;
            name.to_string()
        } else if *counter == u32::MAX {
            panic!("Variable counter overflow");
        } else {
            // name = name${cntr}
            // We use `$`` to avoid having to worry about variables that already have _1 in them in the source code.
            // As `$` is not a valid wgsl identifier.
            let mut s = String::with_capacity(name.len() + 2);
            s.push_str(name);
            s.push('$');
            s.push_str(&counter.to_string());
            *counter += 1;
            s
        }
    }

    /// Mark the access constraints for the access expression indexed by `expr`.
    /// If this is a struct access, then we mark the struct access.
    ///
    /// Used by [`visit_expr`]'s handling of [`AccessIndex`] and [`Access`].
    ///
    /// [`visit_expr`]: Self::visit_expr
    /// [`Access`]: crate::Expression::Access
    /// [`AccessIndex`]: crate::Expression::AccessIndex
    fn make_access(
        &mut self,
        base_expr_handle: crate::Handle<crate::Expression>,
        base_expr: Term,
        index: ExpressionOrLiteral,
        with_constraints: bool, // Give me the source code for the expression...
    ) -> Result<Term, BoundsCheckError> {
        let func_ctx = self.get_current_function();
        let module_info = self.module_info.as_ref().unwrap();
        use crate::proc::TypeResolution;
        let base_expr_info = &func_ctx.info[base_expr_handle].ty;
        let (naga_ty, ref abc_ty) = match *base_expr_info {
            TypeResolution::Handle(ty) => (&module_info.module.types[ty], self[ty].clone()),
            TypeResolution::Value(crate::TypeInner::Pointer { base, space }) => {
                (&module_info.module.types[base], self[base].clone())
            }
            _ => {
                return Err(BoundsCheckError::Unexpected(format!(
                    "{}:{}, Unresolved type used for an AccessIndex base: {:?}",
                    file!(),
                    line!(),
                    base_expr_info
                )));
                // self.make_type(expr_info.ty.inner_with(module_info.module.types))?.into()
            }
        };

        // Macro boilerplate to expand the expression or literal into an expression.
        macro_rules! as_expression {
            ($index:ident) => {
                match $index {
                    ExpressionOrLiteral::Expression(ref e) => e.clone(),
                    ExpressionOrLiteral::Literal(l) => Term::new_literal(l),
                }
            };
        }

        match *abc_ty.as_ref() {
            AbcType::SizedArray { size, .. } => {
                // Add the constraint that the index is less than the size
                let index_literal: Term = as_expression!(index);
                // Note: We can optimize this later on by reusing the same literal for 0.
                if with_constraints {
                    let size_literal: Term = Term::new_literal(size);
                    self.helper.add_tracked_constraint(
                        &index_literal,
                        abc_helper::ConstraintOp::Cmp(abc_helper::CmpOp::Lt),
                        &size_literal,
                        // The expression this comes from...
                        abc_helper::OpaqueMarker::new(&format!("{}[{}]", base_expr, index)),
                    )?;
                    self.helper.add_tracked_constraint(
                        &index_literal,
                        abc_helper::ConstraintOp::Cmp(abc_helper::CmpOp::Geq),
                        &Term::new_literal(0),
                        abc_helper::OpaqueMarker::new(&format!("{}[{}]", base_expr, index)),
                    )?;
                }
                // Make a new expression that is an access to the base and the index.
                Ok(Term::new_index_access(&base_expr, &index_literal))
            }
            AbcType::DynamicArray { ref ty } => {
                let index_literal: Term = as_expression!(index);
                let res = Term::new_index_access(&base_expr, &index_literal);
                if with_constraints {
                    self.helper.add_tracked_constraint(
                        &index_literal,
                        abc_helper::ConstraintOp::Cmp(abc_helper::CmpOp::Geq),
                        &Term::new_literal(0),
                        abc_helper::OpaqueMarker::new(&format!("{}[{}]", base_expr, index)),
                    )?;
                    // We need an expression for the array length..
                    let len_expression = Term::make_array_length(&base_expr);
                    self.helper.add_tracked_constraint(
                        &index_literal,
                        abc_helper::ConstraintOp::Cmp(abc_helper::CmpOp::Lt),
                        // todo: fix this.
                        &len_expression,
                        abc_helper::OpaqueMarker::new(&format!("{}[{}]", base_expr, index)),
                    )?;
                }
                Ok(res)
            }
            AbcType::Struct { ref members } => {
                if let ExpressionOrLiteral::Literal(l) = index {
                    Ok(Term::new_struct_access(
                        &base_expr,
                        match naga_ty.inner {
                            crate::TypeInner::Struct { ref members, .. } => {
                                let member = &members[l as usize];
                                member.name.clone().unwrap()
                            }
                            // should be unreachable.
                            _ => {
                                return Err(BoundsCheckError::Unexpected(format!(
                                    "{}:{}, Unresolved type used for an AccessIndex base: {:?}",
                                    file!(),
                                    line!(),
                                    base_expr_info
                                )));
                            }
                        },
                        abc_ty.clone(),
                    ))
                } else {
                    Err(BoundsCheckError::Unsupported(
                        "Struct access with non-literal index".to_string(),
                    ))
                }
            }

            #[allow(unreachable_patterns)]
            _ => Err(BoundsCheckError::Unsupported(format!(
                "AccessIndex with {:?} as a base type.",
                abc_ty
            ))),
        }
    }

    fn visit_expr_check_only(
        &mut self,
        expr_handle: crate::Handle<crate::Expression>,
    ) -> Result<(), BoundsCheckError> {
        if get_ref!(@func_summary, self)
            .checked_exprs
            .contains(&expr_handle)
        {
            return Ok(());
        }

        let fn_props = get_cur_fn_props!(self, get);

        use crate::Expression as Expr;
        match get_ref!(@func_ctx, self).func.expressions[expr_handle] {
            // Expressions with no children that must be checked.
            Expr::ZeroValue(_)
            | Expr::Constant(_)
            | Expr::Override(_)
            | Expr::FunctionArgument(_)
            | Expr::SubgroupBallotResult
            | Expr::SubgroupOperationResult { .. }
            | Expr::RayQueryProceedResult
            | Expr::WorkGroupUniformLoadResult { .. }
            | Expr::AtomicResult { .. }
            | Expr::CallResult { .. }
            | Expr::Literal(_)
            | Expr::LocalVariable(_)
            | Expr::GlobalVariable(_) => {
                // Nothing to do for these guys!
            }

            // expressions with just one child
            Expr::Splat { value: e, .. }
            | Expr::ArrayLength(e)
            | Expr::Load { pointer: e }
            | Expr::As { expr: e, .. }
            | Expr::Unary { expr: e, .. }
            | Expr::Swizzle { vector: e, .. }
            | Expr::ImageQuery { image: e, .. }
            | Expr::Relational { argument: e, .. }
            | Expr::RayQueryGetIntersection { query: e, .. }
            | Expr::Derivative { expr: e, .. } => {
                self.visit_expr_check_only(e)?;
            }

            // Expressions with two children
            Expr::Binary {
                left: e1,
                right: e2,
                ..
            } => {
                self.visit_expr_check_only(e1)?;
                self.visit_expr_check_only(e2)?;
            }

            // Expressions with three children
            Expr::Select {
                condition: e1,
                accept: e2,
                reject: e3,
            } => {
                self.visit_expr_check_only(e1)?;
                self.visit_expr_check_only(e2)?;
                self.visit_expr_check_only(e3)?;
            }

            Expr::Compose { ref components, .. } => {
                for &comp in components {
                    self.visit_expr_check_only(comp)?;
                }
            }
            Expr::ImageSample {
                image,
                sampler,
                coordinate,
                array_index,
                depth_ref,
                ..
            } => {
                // Iterate over the non-empty expressions, calling `Option.iter()` for the option kinds.
                let optional_exprs = [array_index, depth_ref];
                let mandatory_exprs = [image, sampler, coordinate];
                let exprs = mandatory_exprs
                    .iter()
                    .chain(optional_exprs.iter().filter_map(|e| e.as_ref()));
                for &expr in exprs {
                    self.visit_expr_check_only(expr)?;
                }
            }
            Expr::ImageLoad {
                image,
                coordinate,
                array_index,
                sample,
                level,
            } => {
                let mandatory_exprs = [array_index, sample, level];
                let optional_exprs = [image, coordinate];
                let exprs = mandatory_exprs
                    .iter()
                    .filter_map(|e| e.as_ref())
                    .chain(optional_exprs.iter());

                for &e in exprs {
                    self.visit_expr_check_only(e)?;
                }
            }
            Expr::Math {
                arg,
                arg1,
                arg2,
                arg3,
                ..
            } => {
                for &e in std::iter::once(&arg)
                    .chain([arg1, arg2, arg3].iter().filter_map(|f| f.as_ref()))
                {
                    self.visit_expr_check_only(e)?;
                }
            }

            // The special cases that we actually have to check.
            Expr::AccessIndex { base, index } => {
                let module_info = get_ref!(@module_info, self);
                let expr_info = &get_ref!(@func_ctx, self).info[base].ty;
                if expr_info
                    .inner_with(&module_info.module.types)
                    .is_indexable(module_info.module, self.buffer_config)
                {
                    let base_expr = self.visit_expr(base)?;
                    self.make_access(base, base_expr, ExpressionOrLiteral::Literal(index), true)?;
                } else {
                    self.visit_expr_check_only(base)?;
                }
            }

            Expr::Access { base, index } => {
                // We need to determine if the base resovles to something we care to track.
                // from the info
                let module_info = get_ref!(@module_info, self);
                let expr_info = &get_ref!(@func_ctx, self).info[base].ty;
                if expr_info
                    .inner_with(&module_info.module.types)
                    .is_indexable(module_info.module, self.buffer_config)
                {
                    // Need to drop these to avoid a borrow error when we call visit_expr

                    // get the expression for idx and base
                    let idx_expr = self.visit_expr(index)?;
                    let base_expr = self.visit_expr(base)?;
                    // Now, mark the constraints for this.
                    self.make_access(
                        base,
                        base_expr,
                        ExpressionOrLiteral::Expression(idx_expr),
                        true,
                    )?;
                } else {
                    self.visit_expr_check_only(base)?;
                    self.visit_expr_check_only(index)?;
                }
            }
        }

        Ok(())
    }

    /// Visit an expression in a function, returning a handle to a variable that can be used to refer to the expression.
    ///
    /// If the expression has already been visited, then no work is done and we return the same handle as before.
    /// Otherwise, we visit all sub expressions therein.
    fn visit_expr(
        &mut self,
        expr_handle: crate::Handle<crate::Expression>,
    ) -> Result<Term, BoundsCheckError> {
        // Whether the expression has yet to be checked for its indices.
        let needs_checked = !get_ref!(@func_summary, self)
            .checked_exprs
            .contains(&expr_handle);
        // let e =
        if let Some(e) = get_ref!(@func_summary, self)
            .expressions
            .get(&expr_handle)
            .cloned()
        {
            let e = e.clone();
            if needs_checked {
                self.visit_expr_check_only(expr_handle)?;
            }
            return Ok(e);
        }

        // If the expression is named, then we use a var with that name and the result is an expression over said var.
        // After binding to a variable, we mark the expression's type.
        // This is nice because we can use the type of the expression from the arena?
        // Now we mark the type of this expression we just got
        // When we load an expression, we
        use crate::Expression as Expr;

        let resolved: Term = match self
            .current_fn_info
            .as_ref()
            .map(|f| f.func.expressions[expr_handle].clone())
            .unwrap()
        {
            Expr::Compose { ty, components } => {
                // We need to see what the type of the expression is.
                // if it is a matrix, then we have a 2D vector.
                // if it is a vector, then we have...
                let ty = &get_ref!(@module_info, self).module.types[ty].inner;
                match *ty {
                    crate::TypeInner::Vector { size, scalar } => {
                        // The term we are making is a new `Vector`.
                        let vec_terms = Vec::with_capacity(match size {
                            crate::VectorSize::Bi => 2,
                            crate::VectorSize::Tri => 3,
                            crate::VectorSize::Quad => 4,
                        });
                        // We need to get the scalar for this type

                        for component in components {
                            let term = self.visit_expr(component)?;
                        }
                        Term::new_vector(&vec_terms, scalar.into())
                    }
                    _ => {
                        return Err(BoundsCheckError::Unsupported(format!(
                            "type for Compose: {ty:?}",
                        )));
                    }
                }
            }
            Expr::ArrayLength(p) => {
                let t = self.visit_expr(p)?;
                Term::make_array_length(&t)
            }
            Expr::Unary { op, expr } => {
                let term = self.visit_expr(expr)?;
                match op {
                    crate::UnaryOperator::Negate => {
                        Term::new_unary_op(abc_helper::UnaryOp::Minus, &term)
                    }
                    _ => {
                        return Err(BoundsCheckError::Unsupported(format!("Unary op: {:?}", op)));
                    }
                }
            }
            Expr::Splat { size, value } => Term::new_splat(self.visit_expr(value)?, (size) as u32),
            // For right now, when we see load, we should just return the variable bound to the inner...
            // Although, for 'store', this really needs to mark the current variable name...
            // A 'load' should get the most recent variable name of the expression it is loading from...
            Expr::Load { pointer } => self.visit_expr(pointer)?,
            Expr::Literal(lit) => lit.into(),
            Expr::Constant(c) => self[c].clone(),
            Expr::Override(o) => self[o].clone(),
            Expr::FunctionArgument(idx) => {
                get_ref!(@func_summary, self).arguments[idx as usize].clone()
            }
            Expr::Binary { op, left, right } => {
                let left = self.visit_expr(left)?;
                let right = self.visit_expr(right)?;
                Self::binary_to_abc_expression(op, left, right)?
            }
            Expr::Access { base, index, .. } => {
                let new_base = self.visit_expr(base)?;
                let new_index = self.visit_expr(index)?;
                self.make_access(
                    base,
                    new_base,
                    ExpressionOrLiteral::Expression(new_index),
                    needs_checked,
                )?
            }
            // We should mark the type of the pointer
            // Expr::FunctionArgument(idx) => func_ctx.arguments[*idx as usize].clone(),
            Expr::AccessIndex { base, index } => {
                let new_base = self.visit_expr(base)?;
                self.make_access(
                    base,
                    new_base,
                    ExpressionOrLiteral::Literal(index),
                    needs_checked,
                )?
            }
            Expr::As {
                expr: a,
                kind: s,
                convert: b,
            } => {
                let a = self.visit_expr(a)?;
                use crate::ScalarKind;
                match (s, b) {
                    (ScalarKind::Sint, Some(b)) => {
                        Term::new_cast(a.clone(), abc_helper::AbcScalar::Sint(b))
                    }
                    (ScalarKind::Uint, Some(b)) => {
                        Term::new_cast(a.clone(), abc_helper::AbcScalar::Uint(b))
                    }
                    (ScalarKind::Float, Some(b)) => {
                        Term::new_cast(a.clone(), abc_helper::AbcScalar::Float(b))
                    }
                    (ScalarKind::Bool, _) => Term::new_unit_pred(&a),
                    _ => {
                        return Err(BoundsCheckError::Unsupported(format!(
                            "Cast of type {:?} of size {:?}",
                            s, b
                        )));
                    }
                }
            }
            Expr::GlobalVariable(ref g) => {
                // If the term exists in our global variable map, then we use that.
                if let Some(&(ref term, _)) = get_ref!(@block_ctx, self).global_variable_map.get(g)
                {
                    term.clone()
                } else {
                    self[*g].clone()
                }
            }
            Expr::LocalVariable(ref l) => {
                get_ref!(@block_ctx, self).local_variable_map[l].0.clone()
            }
            Expr::CallResult(ref c) => {
                return Err(BoundsCheckError::Unexpected(
                    "Attempted to visit a call result.".to_string(),
                ))
            }
            Expr::Relational { fun, argument } => {
                use crate::RelationalFunction as R;
                let arg = self.visit_expr(argument)?;
                // This is a vector of booleans, and we need to know of how many terms so that we can expand it.
                // So, get the type of the argument

                // If this is an `All` then we join with Predicate::And
                // If this is an `Any` then we join with Predicate::Or
                let compose_fn = match fun {
                    R::All => Term::new_logical_and,
                    R::Any => Term::new_logical_or,
                    _ => {
                        return Err(BoundsCheckError::Unsupported(format!(
                            "Relational function: {:?}",
                            fun
                        )))
                    }
                };
                // Now, figure out how many terms so we know how many to loop over.
                let module_info = get_ref!(@module_info, self);
                let num_elems = self
                    .get_num_elems(module_info.module, &get_ref!(@func_ctx, self).info[argument].ty)
                    .ok_or(BoundsCheckError::Unexpected(
                        "Could not get number of elements for relational argument".to_string(),
                    ))?;
                // Create a new term that composes the compose function over the kind of term.
                // e.g., if this is an `All`, then this will expand to ((argument[0] && argument[1]) && ... && argument[n])
                // Unsafe is OK here since we know that the number of elements is at least 1.
                unsafe {
                    (0..num_elems)
                        .map(|i| {
                            Term::new_index_access(
                                &arg,
                                &Term::new_literal(abc_helper::Literal::from(i)),
                            )
                        })
                        .by_ref()
                        .reduce(|a, b| compose_fn(&a, &b))
                        .unwrap_unchecked()
                }
            }
            Expr::Math {
                fun,
                arg,
                arg1,
                arg2,
                arg3,
            } => {
                use crate::MathFunction as M;
                match fun {
                    M::Abs => {
                        let arg = self.visit_expr(arg)?;
                        Term::new_abs(&arg)
                    }
                    M::Min if arg1.is_some() => {
                        let arg = self.visit_expr(arg)?;
                        // Safety: we are guarded by arg1 being some.
                        let arg1 = self.visit_expr(unsafe { arg1.unwrap_unchecked() })?;
                        Term::new_min(&arg, &arg1)
                    }
                    M::Max if arg1.is_some() => {
                        let arg = self.visit_expr(arg)?;
                        // Safety: we are guarded by arg1 being some.
                        let arg1 = self.visit_expr(unsafe { arg1.unwrap_unchecked() })?;
                        Term::new_max(&arg, &arg1)
                    }
                    M::Pow if arg1.is_some() => {
                        let arg = self.visit_expr(arg)?;
                        // Safety: we are guarded by arg1 being some.
                        let arg1 = self.visit_expr(unsafe { arg1.unwrap_unchecked() })?;
                        Term::new_pow(&arg, &arg1)
                    }
                    M::Dot if arg1.is_some() => {
                        // Dot product is straightforward.
                        let arg = self.visit_expr(arg)?;
                        let arg1 = self.visit_expr(unsafe { arg1.unwrap_unchecked() })?;
                        Term::new_dot(&arg, &arg1)
                    }
                    _ => {
                        return Err(BoundsCheckError::Unsupported(format!(
                            "Unsupported math function used for value: {:?}",
                            fun
                        )));
                    }
                }
            }
            e => {
                return Err(BoundsCheckError::Unsupported(
                    "Unsupported expression type: ".to_owned() + expression_variant!(e),
                ));
            }
        };

        // If this is a named expression, then we use the name to refer to said expression.
        // Otherwise, the result is the term we evaluated.
        let resolved = if let Some(named_expression) = self
            .get_current_function()
            .func
            .named_expressions
            .get(&expr_handle)
            .cloned()
        {
            let varname = self.next_var_name(named_expression.as_str());
            let expr_var_name = self.helper.declare_var(abc_helper::Var { name: varname })?;

            // Add the equality constraint.
            self.helper.add_constraint(
                &expr_var_name,
                abc_helper::ConstraintOp::Assign,
                &resolved,
            )?;

            // TODO: Figure out if we need to mark the type of the expression?
            // We shouldn't need to do this, right?
            // let info = &func_ctx.info[expr_handle];

            expr_var_name
            // AbcExpression::new_var(var)
        } else {
            resolved
        };
        self.current_fn_summary
            .as_mut()
            .unwrap()
            .expressions
            .insert(expr_handle, resolved.clone());

        Ok(resolved)

        // #[allow(unreachable_code)]
        // Ok(())
    }

    fn update_loop<T: HasName + HasType>(
        &mut self,
        modified_map: &mut FastHashMap<crate::Handle<T>, (Term, bool)>,
        context_map: &mut FastHashMap<crate::Handle<T>, (Term, bool)>,
        condition: &Term,
        arena: &crate::arena::Arena<T>,
        space: &str,
    ) -> Result<(), BoundsCheckError> {
        for (handle, &mut (ref mut old_term, ref mut old_update)) in context_map.iter_mut() {
            let (term, modified) =
                modified_map
                    .remove(handle)
                    .ok_or(BoundsCheckError::Unexpected(
                        "Missing ".to_string() + space + " variable",
                    ))?;
            if !modified {
                continue;
            }
            let new_var = self.mark_var(&arena[*handle], space)?;
        }

        Ok(())
    }

    /// Helper method that updates the context map after an `if-else` statement to update SSA name
    /// for variables that were modified.
    /// Does if-else updating of the context map, for either global variables or local variables.
    ///
    /// This iterates through each of the handles to variables in the context map, and replaces them with
    /// new terms if they were updated in either the accept block or the reject block.
    ///
    /// There are four cases:
    /// 1. The variable was modified in both the accept and reject blocks. The new term is then `select(condition, accept, reject)`
    /// 2. The variable was modified in the accept block only. The new term is then `select(condition, accept, old)`
    /// 3. The variable was modified in the reject block only. The new term is then `select(condition, old, reject)`
    /// 4. The variable was not modified in either block. The term is left as is.
    ///
    /// Any terms that are modified are marked as such in the context map.
    /// Context map itself will hold the new terms.
    /// # Arguments
    /// - `accept_map` Map of variables that may have been modified in the accept block
    /// - `reject_map` Map of variables that may have been modified in the reject block
    /// - `context_map` Map of variables in the current block context (prior to the accept / reject block evaluation)
    /// - `condition` The condition for the `if` statement
    /// - `arena` The arena where the local / global variable exists in the module.
    fn update_if_else<T: HasName + HasType>(
        &mut self,
        mut accept_map: FastHashMap<crate::Handle<T>, (Term, bool)>,
        mut reject_map: FastHashMap<crate::Handle<T>, (Term, bool)>,
        context_map: &mut FastHashMap<crate::Handle<T>, (Term, bool)>,
        condition: &Term,
        arena: &crate::arena::Arena<T>,
        space: &str,
    ) -> Result<(), BoundsCheckError> {
        // We get the `accept` map and the `reject` map depending on if the space is `locals` or `globals`
        for (handle, &mut (ref mut old_term, ref mut old_update)) in context_map.iter_mut() {
            // if we modified it in both blocks, then we make this a select.
            let (accept_term, accept_modified) =
                accept_map
                    .remove(handle)
                    .ok_or(BoundsCheckError::Unexpected(
                        "Missing ".to_string() + space + " variable",
                    ))?;
            let (reject_term, reject_modified) =
                reject_map
                    .remove(handle)
                    .ok_or(BoundsCheckError::Unexpected(
                        "Missing ".to_string() + space + " variable",
                    ))?;
            if !(accept_modified || reject_modified) {
                continue;
            }
            // Create the new var so we can assign to it.
            let new_var = self.mark_var(&arena[*handle], space)?;
            *old_term = new_var.clone();
            *old_update = true;
            let new_term = match (accept_modified, reject_modified) {
                (true, true) => Term::new_select(condition, &accept_term, &reject_term),
                (true, false) => Term::new_select(condition, &accept_term, old_term),
                (false, true) => Term::new_select(condition, old_term, &reject_term),
                _ => {
                    // This should be unreachable.
                    unreachable!();
                }
            };
            // Add the assumption that the new term is equal to the value of the variable.
            self.helper
                .add_assumption(&new_var, abc_helper::ConstraintOp::Assign, &new_term)?;
        }
        Ok(())
    }

    /// Check function will add terms and constraints from the body of the function.
    ///
    /// Local variables are maintained in a map that tracks which blocks have written to them.
    ///
    /// This allows us to do strict SSA renaming for local variables.
    ///
    /// The restrictions on WGSL mean that we can never have more than one pointer to the same memory location
    /// where multiple of them are writes.
    /// This is because pointers to pointers are not allowed. So, while local variables can be pointers,
    /// they can never break ssa.
    ///
    /// So, to check a module, we begin by marking all of the local variables and their types.
    /// This interacts with abc_helper to mark the variables in the constraint system.
    ///
    /// Next, we mark the return type of the function.
    ///
    /// Then, we go build the `block_ctx` struct that is used for SSA renaming.
    /// When a local variable or global variable is written to, we create a new variable in the constraint system
    /// and update our `block_ctx` to point to the new term.
    ///
    /// Any expression referencing a local or global variable will use this new term.
    /// Naga guarantees that any use of the variable that was stored to will have a new load expression reissued.
    /// This fact makes our analysis dramatically easier.
    fn check_function(&mut self, name: &str) -> Result<(), BoundsCheckError> {
        // We need to set everything for current
        // Exit early if the function can kill, as this isn't supported.
        if get_ref!(@func_ctx, self).info.may_kill {
            return Err(BoundsCheckError::Unsupported(
                "Functions that can kill invocations.".to_string(),
            ));
        }

        let mut global_variable_map: FastHashMap<crate::Handle<GlobalVariable>, (Term, bool)> =
            FxHashMap::with_capacity_and_hasher(
                get_ref!(@func_ctx, self).info.global_variable_count(),
                Default::default(),
            );
        for (handle, var) in get_ref!(@module_info, self).module.global_variables.iter() {
            // Here, *any* reads from a global variable in the shared space *must* be marked as killed by the invocation
            // if the function writes to the global variable.
            if let AddressSpace::Storage { access } = var.space {
                if access.contains(crate::StorageAccess::STORE)
                    && get_ref!(@func_ctx, self).info[handle]
                        .intersects(GlobalUse::READ | GlobalUse::WRITE)
                {
                    // We do not add these terms to the global variable map.
                    // When evaluating expressions, when we see a global variable that is not in the global variable map,
                    // Then we know not to issue a constraint for the write.
                    // This ensures the variable is never renamed.

                    // We could maybe be smarter about this by determining the uniformity of the writes to the global variable,
                    // but there are complexities in doing this for buffer like variables.
                    continue;
                }
            }
            global_variable_map.insert(handle, (self[handle].clone(), false));
        }

        // Go through local variables...
        // Make the block context
        let block_ctx = BlockContext {
            local_variable_map: FxHashMap::with_capacity_and_hasher(
                get_ref!(@func_ctx, self).func.local_variables.len(),
                Default::default(),
            ),
            global_variable_map,
        };

        self.current_block_ctx = Some(block_ctx);

        // For local variables, how do we know when we need to initialize them?
        // We need to initialize them the first time they are read from.
        // If they are not marked, then they can be anything and are added to the arena as such.
        for (var_handle, var) in get_ref!(@func_ctx, self).func.local_variables.iter() {
            let lvar_key = var_handle.as_marked_key_with(self.current_path.first().unwrap());

            let var_term = self.mark_var(var, name)?;
            get_ref!(@mut @func_summary, self)
                .local_variabes
                .push(var_term.clone());
            get_ref!(@mut @block_ctx, self)
                .local_variable_map
                .insert(var_handle, (var_term.clone(), false));
            // We do not need to worry about initializing the local variable if it is not marked.
            if !self.visitor_info.marked_exprs.contains(&lvar_key) {
                continue;
            }
            // If there is an init method, then we need to visit it.
            if let Some(init) = var.init {
                let init_term = self.visit_expr(init)?;
                self.helper.add_assumption(
                    &var_term,
                    abc_helper::ConstraintOp::Assign,
                    &init_term,
                )?;
            } else {
                // In this case, we do nothing, as the variable is not initialized.
                // Though if this is wgsl frontend, variables that are not initialized are initialized to 0, right?
                // match on the type of inner.
                use crate::TypeInner as Ty;
                match get_ref!(@module_info, self).module.types[var.ty].inner {
                    Ty::Scalar(s) => {
                        use crate::Scalar;
                        self.helper.add_assumption(
                            &var_term,
                            abc_helper::ConstraintOp::Assign,
                            &match s {
                                Scalar::BOOL => Term::new_literal_false(),
                                Scalar::I32 => Term::new_literal(abc_helper::Literal::I32(0i32)),
                                Scalar::F32 => Term::new_literal(abc_helper::Literal::F32(0.0f32)),
                                Scalar::U32 => Term::new_literal(abc_helper::Literal::U32(0u32)),
                                Scalar::I64 => Term::new_literal(abc_helper::Literal::I64(0i64)),
                                Scalar::U64 => Term::new_literal(abc_helper::Literal::U64(0u64)),
                                Scalar::F64 => Term::new_literal(abc_helper::Literal::F64(0.0f64)),
                                _ => {
                                    return Err(BoundsCheckError::Unsupported(format!(
                                        "Unitialized local variable of type {:?}",
                                        s
                                    )));
                                }
                            },
                        )?;
                    }
                    Ty::Array { .. } | Ty::Vector { .. } => {
                        // Note: Uninitialized arrays are really initialized to 0.
                        // However, for now, we leave them as undefined.
                    }
                    ref e => {
                        return Err(BoundsCheckError::Unsupported(format!(
                            "Unitialized local variable of type {:?}",
                            e
                        )));
                    }
                }
            }
        }

        // Now we visit the function block.
        // tricky with lifetimes. visit_Block will need to borrow self mutably, though `Block` itself should never be changed.
        self.visit_Block(&get_ref!(@func_ctx, self).func.body)?;

        if let Some(crate::FunctionResult { ty, .. }) = get_ref!(@func_ctx, self).func.result {
            let ty = self[ty].clone();
            self.helper.mark_return_type(&ty)?;
        }

        self.current_block_ctx = None;

        Ok(())
    }

    /// Convert a binary operator to an ABC expression
    fn binary_to_abc_expression(
        op: crate::BinaryOperator,
        lhs: Term,
        rhs: Term,
    ) -> Result<Term, BoundsCheckError> {
        use crate::BinaryOperator;
        use abc_helper::BinaryOp;
        use abc_helper::CmpOp;
        use abc_helper::Predicate;
        if let Ok(binop) = op.try_into() {
            Ok(Term::new_binary_op(binop, &lhs, &rhs))
        } else if let Ok(cmpop) = op.try_into() {
            Ok(Term::new_comparison(cmpop, &lhs, &rhs))
        } else {
            match op {
                BinaryOperator::LogicalAnd => Ok(Term::new_logical_and(&lhs, &rhs)),
                BinaryOperator::LogicalOr => Ok(Term::new_logical_or(&lhs, &rhs)),
                _ => Err(BoundsCheckError::Unsupported(
                    "Unsupported binary operator".to_string(),
                )),
            }
        }
    }

    /// Determine the number of elements of the vector type.
    ///
    /// This works on the TypeResolution to figure out how many elements.
    ///
    /// If this is not a vector, then we return `None`
    fn get_num_elems(&self, module: &Module, ty: &crate::proc::TypeResolution) -> Option<u32> {
        // Determine the number of elements of the type, assuming the type is a vector.
        use crate::proc::TypeResolution as Tr;
        use crate::TypeInner as Ty;
        let ty_inner = match *ty {
            Tr::Handle(h) => &module.types[h].inner,
            Tr::Value(ref t) => t,
        };
        match *ty_inner {
            Ty::Vector {
                size: crate::VectorSize::Bi,
                ..
            } => Some(2u32),
            Ty::Vector {
                size: crate::VectorSize::Tri,
                ..
            } => Some(3u32),
            Ty::Vector {
                size: crate::VectorSize::Quad,
                ..
            } => Some(4u32),
            _ => None,
        }
    }

    /// Resolve a global expression to an AbcExpression from a handle.
    ///
    /// If the expression has already been resolved, this will return a handle to it.
    /// Otherwise, it will create the expression.
    ///
    /// This assumes global scope. This restricts the kinds of expressions that are possible.
    /// That is, expressions can only be const, and can only refer to other expressions
    /// Loads are not permissible.
    fn global_expression_resolution(
        &mut self,
        expr_handle: crate::Handle<crate::Expression>,
        module: &ModuleWithInfo,
    ) -> Result<Term, BoundsCheckError> {
        use crate::Expression as Expr;
        use AbcExpression as ABCExpr;

        // If we have already resolved the expression, then just return it.
        if let Some(expr) = self.global_exprs.get(&expr_handle) {
            return Ok(expr.clone());
        }
        // Otherwise, we need to resolve it.
        // This means creating the expression.

        let expr = &module.module.global_expressions[expr_handle];

        // It's annoying because naga's decision to use handles means we have to write
        // this logic twice. Once for the global expressions and once for the function expressions.
        let res: Term = match *expr {
            Expr::Literal(t) => t.into(),
            Expr::Constant(c) => self[c].clone(),
            Expr::Binary { op, left, right } => {
                let left = self.global_expression_resolution(left, module)?;
                let right = self.global_expression_resolution(right, module)?;
                Self::binary_to_abc_expression(op, left, right)?
                // A binary op with a boolean result maps to a predicate
                // Otherwise, it maps to a binary op.
            }
            _ => {
                let msg = String::from("Unsupported global expression type: ")
                    + format!("{:?}", expression_variant!(*expr)).as_str();
                return Err(BoundsCheckError::Unsupported(msg));
            }
        };
        self.global_exprs.insert(expr_handle, res.clone());
        Ok(res)
    }

    fn make_function_summary(
        &self,
        fun: &crate::Function,
    ) -> Result<PartialFunctionSummary, BoundsCheckError> {
        let nargs: u8 = fun.arguments.len().try_into().map_err(|_| {
            BoundsCheckError::Unsupported("Too many arguments to function.".to_string())
        })?;
        Ok(PartialFunctionSummary {
            arguments: Vec::with_capacity(nargs as usize),
            expressions: crate::FastHashMap::default(),
            local_variabes: Vec::with_capacity(fun.local_variables.len()),
            ret_ty: match fun.result {
                Some(crate::FunctionResult { ty, .. }) => self[ty].clone(),
                None => self.helper.none_type(),
            },
            nargs,
            checked_exprs: crate::FastHashSet::default(),
        })
    }

    /// Adds arguments to the current active summary. Also gets their types.
    fn make_arg(
        &mut self,
        arg: &FunctionArgument,
        fun: &crate::Function,
        pos: usize,
    ) -> Result<Term, BoundsCheckError> {
        // Name doesn't have to be unique. It will be prefixed by `@` in the ABC.
        let name = arg
            .to_name()
            .clone()
            .unwrap_or(String::from("arg") + &pos.to_string());
        // Get the variable handle..
        let var = self
            .helper
            .add_argument(name, &self.types[arg.to_type().index()].clone())?;
        Ok(var)
    }

    fn func_to_name<T: ToString>(fun: &crate::Function, suffix: T) -> String {
        if let Some(name) = fun.name.as_ref() {
            name.clone()
        } else {
            let mut name = String::from("$anon_func_");
            name.push_str(&suffix.to_string());
            name
        }
    }

    fn resolve_global_expression(&mut self) {}
    pub fn abc_impl(
        &mut self,
        module: &'module Module,
        validation_info: &'module ModuleInfo,
    ) -> Result<(), BoundsCheckError> {
        // Step 1: Call the visitor to populate the expressions we do and do not need to visit.
        self.visitor_info =
            super::visitor::process_module(module, validation_info, self.address_space_config)?;

        // Temporarily, we need to assert that the visitor info is correct.
        // We have an access index in the store.
        // The store is a store to a marked variable.

        self.module_info = Some(ModuleWithInfo {
            module,
            validation_info,
        });

        // Now, when we go to visit the module, we ONLY evaluate expressions that are marked.
        // All other expressions are ignored.

        // That means that we should never emit a constraint for an expression that is not marked.

        // Clear the types...
        self.types = Vec::with_capacity(module.types.len());
        for (ty_handle, ty) in module.types.iter() {
            let ty = self.make_type(ty)?;
            self.types.push(ty.into());
        }
        // Global expressions are only computed the first time they are accessed.
        //

        let module_info = ModuleWithInfo {
            module,
            validation_info,
        };

        self.constants = Vec::with_capacity(module.constants.len());
        for (var_handle, var) in module.constants.iter() {
            let cnst = self.mark_var(var, "glbl")?;
            self.constants.push(cnst.clone());
            // Push the initialization of the constant as a constraint.
            // Any expressions here can only refer to previously defined constants, right?

            // Resolve the initialization to an expression handle
            let expr = self.global_expression_resolution(var.init, &module_info)?;

            // Mark the constraint of the initialization.
            self.helper
                .add_constraint(&cnst, abc_helper::ConstraintOp::Assign, &expr)?;
        }
        self.overrides = Vec::with_capacity(module.overrides.len());
        for (var_handle, var) in module.overrides.iter() {
            let ovr = self.mark_var(var, "glbl")?;
            self.overrides.push(ovr);
        }

        for (var_handle, var) in module.global_variables.iter() {
            let new_var = self.mark_var(var, "glbl")?;
            self.global_vars.push(new_var.clone());
            // Now, we need to mark the initializer of the global variable.
            if let Some(init) = var.init {
                let expr = self.global_expression_resolution(init, &module_info)?;
                self.helper
                    .add_constraint(&new_var, abc_helper::ConstraintOp::Assign, &expr)?;
            }
        }

        for (fun_handle, fun) in module.functions.iter() {
            // We are visiting a function. So mark the current path.
            self.push_path_part(StatementPathPart::Function(fun_handle));

            // Get the function name
            let func_name = Self::func_to_name(fun, fun_handle.index());
            log_info!("Checking function: {}", func_name);
            // Make the partial summary.
            let mut partial_summary = self.make_function_summary(fun)?;
            let nargs = partial_summary.nargs;
            self.helper.begin_summary(func_name.clone(), nargs)?;
            for (pos, arg) in fun.arguments.iter().enumerate() {
                let var = self.make_arg(arg, fun, pos)?;
                partial_summary.arguments.push(var);
            }

            self.current_fn_info = Some(FunctionWithInfo {
                func: fun,
                info: &validation_info[fun_handle],
                key: FnKey::Function(fun_handle),
            });

            self.current_fn_summary = Some(partial_summary);

            // Begin the summary

            // Add the function arguments
            // This is done outside of the `check_function` method because
            // entry points do something special with their arguments.

            // Now begin the common function handling logic
            self.check_function(&func_name)?;
            self.current_fn_info = None;
            let summary_handle = self.helper.end_summary()?;
            self.functions.push(
                self.current_fn_summary
                    .take()
                    .unwrap()
                    .into_function_summary(summary_handle),
            );
            self.pop_path_part();
        }

        // Entry points contain function summaries.
        for (pos, ep) in module.entry_points.iter().enumerate() {
            self.push_path_part(StatementPathPart::EntryPoint(EntryPointIndex(pos)));
            log_info!("Checking entry point: {}", ep.name);
            // An entry
            let func_name = ep.name.clone();
            let partial_summary = self.make_function_summary(&ep.function)?;
            let nargs = partial_summary.nargs;
            self.helper.begin_summary(func_name.clone(), nargs)?;
            let ep_info = validation_info.get_entry_point(pos);

            self.current_fn_info = Some(FunctionWithInfo {
                func: &ep.function,
                info: &validation_info.get_entry_point(pos),
                key: FnKey::EntryPoint(pos.into()),
            });

            self.current_fn_summary = Some(partial_summary);

            for (pos, arg) in ep.function.arguments.iter().enumerate() {
                let var = self.make_arg(arg, &ep.function, pos)?;
                // This arg *must* be a bound.
                use crate::Binding;
                match arg.binding {
                    Some(Binding::BuiltIn(crate::BuiltIn::LocalInvocationId)) => {
                        // If this is a local invocation id, then we add the constraint on its range from the workgroup information
                        // that we already have.
                        for (high, dim) in ep.workgroup_size.iter().zip(0u32..=2u32) {
                            // make a term for the access to the 0th element of the expression.
                            let access_term = Term::new_index_access(&var, &Term::new_literal(dim));
                            self.helper.mark_range(&access_term, 0u32, *high - 1)?;
                            // We need to mark the range of the variable.
                        }
                    }
                    Some(Binding::BuiltIn(t)) => {
                        log_info!("Built-in binding not yet accounted for: {:?}", t);
                    }
                    Some(_) => {
                        return Err(BoundsCheckError::Unsupported(
                            "Entry point argument with a non built-in binding.".to_string(),
                        ));
                    }
                    None => {
                        // According to naga, this should never happen
                        unreachable!();
                    }
                };
                get_ref!(@mut @func_summary, self).arguments.push(var);
            }
            // For entry points, we need to make a new summary.

            self.check_function(&func_name)?;

            let summary_handle = self.helper.end_summary()?;
            // End the summary
            self.entry_points.push(
                self.current_fn_summary
                    .take()
                    .unwrap()
                    .into_function_summary(summary_handle),
            );

            self.pop_path_part();
        }

        Ok(())
    }
}

/// This visitor issues the constraints for the bounds checker.
impl StatementVisitor<BoundsCheckError> for BoundsChecker<'_> {
    fn visit_Break(&mut self) -> Result<(), BoundsCheckError> {
        self.helper.mark_break()?;
        Ok(())
    }

    fn visit_Continue(&mut self) -> Result<(), BoundsCheckError> {
        self.helper.mark_continue()?;
        Ok(())
    }

    /// Checks if the statement is marked as requiring a visit, and, if so, calls
    /// the appropriate visitor method.
    fn visit_Statement(&mut self, stmt: &Statement) -> Result<(), BoundsCheckError> {
        log_trace!("Visiting statement: {stmt:?}");
        // Check if the statement is marked as needing to be visited.
        // If it is, then we visit it. Otherwise, we don't.
        if self
            .visitor_info
            .statement_map
            .get(&self.current_path)
            .is_some_and(|props| props.is_marked())
        {
            self.default_visit_Statement(stmt)
        } else {
            Ok(())
        }
    }

    /// When we see a store, we have to deal with SSA renaming.
    /// Luckily, WGSL has some restrictions about aliases that reduce the complexity of stores.
    ///
    /// When we see a store, we tell the constraint helper that we need a new variable.
    /// We then add an assumption that the new variable's value is equal to the value being stored.
    ///
    /// Then, we update an internal map that maps handles to Local and Global variables (the only things that can be modified)
    /// to point to this new term we requested from the constraint helper.
    ///
    /// All `Load` expressions actually refer to this map to determine which term they resolve to.
    /// That is, if we see something like this:
    /// ```wgsl
    /// var a = 4
    /// a = a + 1
    /// b = 2*a
    /// ```
    /// Then that would look like this in our constraint system:
    ///```wgsl
    /// a = 4
    /// a_1 = a + 1  // At this line, we would update our internal map for a.
    /// b = 2*a_1
    ///```
    ///
    /// [`visit_statement`]: Self::visit_statement
    fn visit_Store(
        &mut self,
        pointer: crate::Handle<crate::Expression>,
        value: crate::Handle<crate::Expression>,
    ) -> Result<(), BoundsCheckError> {
        use crate::proc::TypeResolution as KIND;
        use crate::Expression as E;
        use crate::TypeInner;
        // For the store, we first check if we need to visit the expression.
        // Step 1: Determine the expression we are storing to.

        if !self
            .visitor_info
            .statement_map
            .get(&self.current_path)
            .expect("visited store statement should exist in statement map")
            .writes_to_marked()
        {
            if self
                .visitor_info
                .statement_map
                .get(&self.current_path)
                .unwrap()
                .is_marked()
            {
                self.visit_expr_check_only(pointer)?;
                self.visit_expr_check_only(value)?;
            }
            return Ok(());
        }

        let base_term = self.visit_expr(pointer)?;
        let mut value_term = self.visit_expr(value)?;

        let mut current = pointer;
        let e: crate::Handle<crate::Expression>;

        macro_rules! get_ref {
            (@func_summary) => {
                self.current_fn_summary
                    .as_ref()
                    .expect("function summary should exist in visitors")
            };
            (@mut @func_summary) => {
                self.current_fn_summary
                    .as_mut()
                    .expect("function summary should exist in visitors")
            };
            (@module_info) => {
                self.module_info
                    .as_ref()
                    .expect("module info should exist in visitors")
            };
            (@func_ctx) => {
                self.current_fn_info
                    .as_ref()
                    .expect("function context should exist in visitors")
            };
        }
        loop {
            // We have to remove, from the function summary, any expression we are about to overwrite, if it exists, so that we don't use stale information.
            get_ref!(@mut @func_summary).expressions.remove(&current);
            match get_ref!(@func_ctx).func.expressions[current] {
                E::AccessIndex { base, index } => {
                    // Naga allows AccessIndex to correspond to either a struct, or an array with a constant offset.
                    // Unfortunately, this complicates how we have to handle access index expressions.
                    // Here, ty_inner represents the type of expression behind the pointer.
                    // We expect this to be a pointer. So if it isn't, we reject it.
                    let ty_inner = get_ref!(@func_ctx).info[current]
                        .ty
                        .inner_with(&self.module_info.unwrap().module.types);
                    // Now that we know whether the expression corresponds to a struct assignment or a field access,
                    // we can match the type of the struct.
                    match *ty_inner {
                        TypeInner::Struct { ref members, .. } => {
                            value_term = Term::new_struct_store(
                                get_ref!(@func_summary)[base].clone(),
                                index as usize,
                                value_term.clone(),
                            )
                        }
                        _ => {
                            value_term = Term::new_store(
                                get_ref!(@func_summary)[base].clone(),
                                index.into(),
                                value_term.clone(),
                            )
                        }
                    }
                    current = base;
                }
                E::Access { base, index } => {
                    value_term = Term::new_store(
                        get_ref!(@func_summary)[base].clone(),
                        get_ref!(@func_summary)[index].clone(),
                        value_term.clone(),
                    );
                    current = base;
                }
                E::GlobalVariable(g)
                    if !self
                        .current_block_ctx
                        .as_ref()
                        .unwrap()
                        .global_variable_map
                        .contains_key(&g) =>
                {
                    // If the global variable does not appear in our map, then we do not mark the assumption.
                    // This allows us to be pessimistic about the domain of global variables that
                    // may have been written to by other blocks / threads.
                    // TODO: figure out if we want to actually issue a constraint against the original global variable.
                    break Ok(());
                }
                E::LocalVariable(l) => {
                    // Get a new term for the var.
                    // We have to drop our references before this call.
                    let new_term = self.mark_var(
                        &get_ref!(@func_ctx).func.local_variables[l].clone(),
                        "local",
                    )?;
                    self.helper.add_assumption(
                        &new_term,
                        abc_helper::ConstraintOp::Assign,
                        &value_term,
                    )?;
                    let Some(ref mut block_ctx) = self.current_block_ctx else {
                        unreachable!("Block context should be initialized during visit");
                    };
                    block_ctx.local_variable_map.insert(l, (new_term, true));
                    break Ok(());
                }
                E::GlobalVariable(g) => {
                    // Get a new term for the var.
                    let new_term = self
                        .mark_var(&get_ref!(@module_info).module.global_variables[g], "global")?;
                    self.helper.add_assumption(
                        &new_term,
                        abc_helper::ConstraintOp::Assign,
                        &value_term,
                    )?;
                    let Some(ref mut block_ctx) = self.current_block_ctx else {
                        unreachable!("Block context should be initialized during visit");
                    };
                    block_ctx.global_variable_map.insert(g, (new_term, true));
                    break Ok(());
                }
                E::FunctionArgument(a) => {
                    break Err(BoundsCheckError::Unsupported(
                        "Store to a function argument".to_string(),
                    ));
                }
                _ => {
                    unreachable!(
                        "Store statement with a pointer type that is not Access,\
                        AccessIndex, LocalVariable, GlobalVariable, or FunctionArgument"
                    );
                }
            }
        }
    }

    /// Visit the block.
    ///
    /// # Safety
    ///
    /// This function calls [`get_visitor_info`], and thus requires that `self.visitor_info` is Some.
    ///
    /// [`get_visitor_info`]: Self::get_visitor_info
    fn visit_Block(&mut self, block: &crate::Block) -> Result<(), BoundsCheckError> {
        // Check if we need to be visited.
        let mut index = 0;
        // Safety: We are in a visitor, meaning we have a visitor info.

        for stmt in block.iter() {
            // Emits are not marked, and don't contribute to the index.
            if let Statement::Emit(ref r) = *stmt {
                self.visit_Emit(r)?;
                continue;
            }
            // Safety: Caller must ensure that `self.visitor_info` is Some.
            self.push_path_part(StatementPathPart::Index(index));
            // If visit_statement returns false, that means we hit control flow and should stop processing more
            // elements in the block (e.g, we hit a `break`/`return`/`continue`).
            self.visit_Statement(stmt)?;
            // Check if that was a terminator.
            // We need to stop if this is marked as being a terminator.
            let was_terminator = self
                .visitor_info
                .statement_map
                .get(&self.current_path)
                .expect("visited block statement should exist in statement map")
                .is_terminator();
            self.pop_path_part();
            if was_terminator {
                break;
            }
            index += 1;
        }

        Ok(())
    }

    fn visit_If(
        &mut self,
        condition: crate::Handle<crate::Expression>,
        accept: &crate::Block,
        reject: &crate::Block,
    ) -> Result<(), BoundsCheckError> {
        let condition = self.visit_expr(condition)?;
        // We need two fresh block contexts with the write set reset.

        let mut old_ctx = self
            .current_block_ctx
            .take()
            .expect("Block context must exist after visiting");

        let mut accept_ctx = old_ctx.reset_writes();
        let mut reject_ctx = accept_ctx.clone();

        if !accept.is_empty() {
            self.push_path_part(StatementPathPart::Accept);
            self.helper.begin_predicate_block(&condition)?;

            // Before visiting the block, we have to replace block ctx with accept context.
            self.current_block_ctx = Some(accept_ctx);
            self.visit_Block(accept)?;
            accept_ctx = self
                .current_block_ctx
                .take()
                .expect("Block context must exist after visiting");
            self.helper.end_predicate_block()?;
            self.pop_path_part();
        }
        if !reject.is_empty() {
            self.push_path_part(StatementPathPart::Reject);
            self.helper
                .begin_predicate_block(&Term::new_not(&condition))?;
            self.current_block_ctx = Some(reject_ctx);
            self.visit_Block(reject)?;
            self.helper.end_predicate_block()?;
            self.pop_path_part();
            reject_ctx = self
                .current_block_ctx
                .take()
                .expect("Block context must exist after visiting");
        }

        let BlockContext {
            local_variable_map: accept_locals,
            global_variable_map: accept_globals,
        } = accept_ctx;
        let BlockContext {
            local_variable_map: reject_locals,
            global_variable_map: reject_globals,
        } = reject_ctx;

        // We need current function context's local variable map.
        // Now we update the block context with the new writes.
        // We use a select expression here.
        // We need to repeat this for both the local and global variables...
        self.update_if_else(
            accept_locals,
            reject_locals,
            &mut old_ctx.local_variable_map,
            &condition,
            &self.get_current_function().func.local_variables.clone(),
            "local",
        )?;
        self.update_if_else(
            accept_globals,
            reject_globals,
            &mut old_ctx.global_variable_map,
            &condition,
            &self
                .module_info
                .as_ref()
                .unwrap()
                .module
                .global_variables
                .clone(),
            "global",
        )?;

        self.current_block_ctx = Some(old_ctx);

        Ok(())
    }

    fn visit_Call(
        &mut self,
        function: crate::Handle<crate::Function>,
        arguments: &[crate::Handle<crate::Expression>],
        result: Option<crate::Handle<crate::Expression>>,
    ) -> Result<(), BoundsCheckError> {
        // Start by getting the function we are invoking, so that we error early if the function hasn't been looked at yet.
        let called_func =
            self.functions
                .get(function.index())
                .ok_or(BoundsCheckError::Unexpected(
                    "Reference to a function that has not been declared.".to_string(),
                ))?;
        let handle = called_func.handle.clone();
        // Using collect looks cleaner, but it's slower since we know the capacity of the vector.
        let mut args = Vec::with_capacity(arguments.len());
        for &arg in arguments {
            let arg = self.visit_expr(arg)?;
            args.push(arg);
        }

        if let Some(result) = result {
            // If there is a result, we store the handle to expression that lets us refer to it.
            let result_name = {
                let func = self
                    .current_fn_info
                    .as_ref()
                    .expect("Function summary should exist during visit")
                    .func;
                if let Some(name) = func.named_expressions.get(&result) {
                    self.next_var_name(name)
                } else {
                    let mut name = String::from("$anon_expr_");
                    name.push_str(&result.index().to_string());
                    name
                }
            };
            let var = self
                .helper
                .declare_var(abc_helper::Var { name: result_name })?;
            let Some(ref mut func_summary) = self.current_fn_summary else {
                unreachable!("Function summary should be initialized during visit");
            };
            func_summary
                .expressions
                .insert(result, self.helper.make_call(&handle, args, Some(&var))?);
        } else {
            // If there is no result, we just make the call.
            self.helper.make_call(&handle, args, None)?;
        };

        Ok(())
    }

    /// Marks the return value of a function.
    fn visit_Return(
        &mut self,
        value: Option<crate::Handle<crate::Expression>>,
    ) -> Result<(), BoundsCheckError> {
        match value {
            Some(v) => {
                // Note that we should only visit the return if we are marked.
                // I need to get the current function as a key....
                if let &StatementPathPart::Function(f) = self
                    .current_path
                    .first()
                    .expect("Path should not be empty in visitors")
                {
                    // If we are marked, then we are used for our return result, and we need to resolve the expression.
                    if self
                        .visitor_info
                        .marked_exprs
                        .contains(&MarkedExprKey::Function(f))
                    {
                        let expr = self.visit_expr(v)?;
                        self.helper.mark_return(Some(expr))?;
                        return Ok(());
                    }
                }
                self.helper.mark_return(None)
            }
            None => self.helper.mark_return(None),
        }?;

        Ok(())
    }

    /// Visits `predicate` if it is some, for access indices only.
    ///
    /// # Errors
    /// Propagates any errors from calling `self.visit_expr_check_only(predicate)`.
    fn visit_SubgroupBallot(
        &mut self,
        result: crate::Handle<crate::Expression>,
        predicate: Option<crate::Handle<crate::Expression>>,
    ) -> Result<(), BoundsCheckError> {
        if let Some(predicate) = predicate {
            self.visit_expr_check_only(predicate)
        } else {
            Ok(())
        }
    }

    /// Checks for the adherence to a supported loop pattern, and visits containing statements if it is supported.
    ///
    /// # Errors
    /// [`BoundsCheckError::UnsupportedLoopStructure`] if the loop does not adhere to the supported pattern.
    ///
    /// [`BoundsCheckError::UnsupportedLoopStructure`]: BoundsCheckError::UnsupportedLoopStructure
    fn visit_Loop(
        &mut self,
        body: &crate::Block,
        continuing: &crate::Block,
        break_if: Option<crate::Handle<crate::Expression>>,
    ) -> Result<(), BoundsCheckError> {
        use crate::Expression as E;
        use crate::Statement as S;
        if break_if.is_some() {
            return Err(BoundsCheckError::Unsupported(
                "Loop with a non empty break_if".to_string(),
            ));
        }
        if body.is_empty() {
            return Err(BoundsCheckError::Unsupported(
                "Loop with an empty body".to_string(),
            ));
        }
        self.model_std_for_loop(body, continuing, break_if)
    }

    /// Visits the `pointer` and `value` expressions for access indices only.
    ///
    /// # Errors
    /// [`BoundsCheckError::Unsupported`] if the atomic operation writes to a marked variable.
    ///
    /// [`BoundsCheckError::Unsupported`]: BoundsCheckError::Unsupported
    fn visit_Atomic(
        &mut self,
        pointer: crate::Handle<crate::Expression>,
        fun: crate::AtomicFunction,
        value: crate::Handle<crate::Expression>,
        result: Option<crate::Handle<crate::Expression>>,
    ) -> Result<(), BoundsCheckError> {
        // Atomic is supported unless the variable it writes to is marked.
        let props = self
            .visitor_info
            .statement_map
            .get(&self.current_path)
            .expect("visited atomic statement should exist in statement map");
        if props.writes_to_marked() {
            Err(BoundsCheckError::Unsupported(
                "Atomic operation writing to a marked variable".to_string(),
            ))
        } else {
            self.visit_expr_check_only(pointer)?;
            self.visit_expr_check_only(value)
        }
    }

    /// Currently unsupported
    fn visit_Switch(
        &mut self,
        selector: crate::Handle<crate::Expression>,
        cases: &Vec<crate::SwitchCase>,
    ) -> Result<(), BoundsCheckError> {
        // let selector = self.visit_expr(selector)?;
        // Switch statements kind of suck.
        // This is because we have `default` which is a catch-all,
        // and is hard to add constraints for.
        Err(BoundsCheckError::Unsupported(
            "Switch statement".to_string(),
        ))
    }

    /// Currently unsupported.
    fn visit_Kill(&mut self) -> Result<(), BoundsCheckError> {
        Err(BoundsCheckError::Unsupported("Kill statement".to_string()))
    }

    /// Visits `image`, `coordinate`, `array_index`, and `value` expressions for access indices only.
    fn visit_ImageStore(
        &mut self,
        image: crate::Handle<crate::Expression>,
        coordinate: crate::Handle<crate::Expression>,
        array_index: Option<crate::Handle<crate::Expression>>,
        value: crate::Handle<crate::Expression>,
    ) -> Result<(), BoundsCheckError> {
        self.visit_expr_check_only(image)?;
        self.visit_expr_check_only(coordinate)?;
        if let Some(array_index) = array_index {
            self.visit_expr_check_only(array_index)?;
        }
        self.visit_expr_check_only(value)
    }

    fn visit_SubgroupGather(
        &mut self,
        mode: crate::GatherMode,
        argument: crate::Handle<crate::Expression>,
        result: crate::Handle<crate::Expression>,
    ) -> Result<(), BoundsCheckError> {
        self.visit_expr_check_only(argument)
    }

    /// Visits the `pointer` expression to emit constraints for access indices only.
    fn visit_SubgroupCollectiveOperation(
        &mut self,
        op: crate::SubgroupOperation,
        collective_op: crate::CollectiveOperation,
        argument: crate::Handle<crate::Expression>,
        result: crate::Handle<crate::Expression>,
    ) -> Result<(), BoundsCheckError> {
        self.visit_expr_check_only(argument)
    }

    /// Visits the `pointer` expression to emit constraints for access indices only.
    fn visit_RayQuery(
        &mut self,
        query: crate::Handle<crate::Expression>,
        fun: &crate::RayQueryFunction,
    ) -> Result<(), BoundsCheckError> {
        self.visit_expr_check_only(query)
    }

    /// Visits the `pointer` expression to emit constraints for access indices only.
    fn visit_WorkGroupUniformLoad(
        &mut self,
        pointer: crate::Handle<crate::Expression>,
        result: crate::Handle<crate::Expression>,
    ) -> Result<(), BoundsCheckError> {
        self.visit_expr_check_only(pointer)
    }

    /// This visitor has nothing to do for barriers.
    fn visit_Barrier(&mut self, barrier: crate::Barrier) -> Result<(), BoundsCheckError> {
        // For barriers, we don't need to do anything.
        // We aren't a race checker.
        Ok(())
    }
}

/// This is our loop analysis that we use to determine if we can support the loop.
///
/// It is lengthy and ugly, and is in desperate need of refactoring.
impl BoundsChecker<'_> {
    /// Loop pattern 1 is where we have a loop that starts with 2 emits: the first is the emit of the local variable that
    /// is the induction variable,
    /// and the second is an expression consisting of the loop condition.
    fn model_std_for_loop(
        &mut self,
        body: &crate::Block,
        continuing: &crate::Block,
        break_if: Option<crate::Handle<crate::Expression>>,
    ) -> Result<(), BoundsCheckError> {
        // Check that the first two expressions are emits.
        let mut body_iter = body.iter();
        let (load_handle, lvar_expr_handle, lvar_handle) = body_iter
            .next()
            .and_then(|stmt| {
                if let Statement::Emit(ref r1) = *stmt {
                    if r1.index_range().len() == 1 {
                        let e1 = r1.clone().next()?;
                        if let crate::Expression::Load { pointer } =
                            get_ref!(@func_ctx, self).func.expressions[e1]
                        {
                            // the expression representing the local variable...
                            if let crate::Expression::LocalVariable(lvar) =
                                get_ref!(@func_ctx, self).func.expressions[pointer]
                            {
                                return Some((e1, pointer, lvar));
                            }
                        }
                    }
                }
                None
            })
            .ok_or(BoundsCheckError::UnsupportedLoopStructure)?;

        // Second emit must be loop condition
        let loop_cond_handle = body_iter
            .next()
            .and_then(|stmt| {
                if let &Statement::Emit(ref r2) = stmt {
                    if r2.index_range().len() == 1 {
                        let e2 = r2.clone().next()?;
                        if let crate::Expression::Binary {
                            op:
                                crate::BinaryOperator::Equal
                                | crate::BinaryOperator::NotEqual
                                | crate::BinaryOperator::Less
                                | crate::BinaryOperator::LessEqual
                                | crate::BinaryOperator::Greater
                                | crate::BinaryOperator::GreaterEqual,
                            right,
                            left,
                        } = get_ref!(@func_ctx, self).func.expressions[e2]
                        {
                            if right == load_handle || left == load_handle {
                                return Some(e2);
                            }
                        }
                    }
                }
                None
            })
            .ok_or(BoundsCheckError::UnsupportedLoopStructure)?;

        // Track the index of the statements in body iter. Needed to know the current path.
        let mut body_iter_idx = 0;
        // loop_cond_handle is the condition of the loop.
        // Now we check that the next statement is an if statement, conditioned on the loop condition,
        // whose reject is a break.
        // This is the for loop pattern.
        match body_iter.next() {
            Some(&Statement::If {
                condition,
                ref accept,
                ref reject,
            }) if condition == loop_cond_handle
                && accept.is_empty()
                && reject.len() == 1
                && matches!(reject[0], Statement::Break) =>
            {
                body_iter_idx += 1;
                Ok(())
            }
            _ => Err(BoundsCheckError::UnsupportedLoopStructure),
        }?;
        // The rest of the body iter should probably be visited now.

        // Now check if the `continuing` block is as we expect.

        let mut continuing_iter = continuing.iter();
        // In the continuing block, we expect a single emit with two expressions. The first must be a load to the induction variable.
        let (store_handle_expr, update_handle_expr) = match continuing_iter
            .next()
            .ok_or(BoundsCheckError::UnsupportedLoopStructure)?
        {
            &Statement::Emit(ref r) => {
                // r must be two expressions. The first is a load to the induction variable, the second is the expression that
                // updates the induction variable.
                if r.index_range().len() != 2 {
                    return Err(BoundsCheckError::UnsupportedLoopStructure);
                }
                // the first expression must be a load to the induction variable.
                match r.first_and_last() {
                    Some((load_handle, update_handle)) if matches!(get_ref!(@func_ctx, self).func.expressions[load_handle], crate::Expression::Load { pointer } if pointer == lvar_expr_handle) => {
                        Ok((load_handle, update_handle))
                    }
                    _ => Err(BoundsCheckError::UnsupportedLoopStructure),
                }
            }
            _ => Err(BoundsCheckError::UnsupportedLoopStructure),
        }?;

        // Expected structure: the next statement in `continuing` is a store where the pointer is the induction variable and the value is the
        // second expression that was just emitted.
        // same expression that was just emitted,
        if !matches!(
            continuing_iter.next(),
            Some(&Statement::Store { pointer, value })
            if pointer == lvar_expr_handle && value == update_handle_expr
        ) {
            return Err(BoundsCheckError::UnsupportedLoopStructure);
        };

        // At this point, the structure of the loop is as expected. Now, we just issue the proper stores that model it.

        // Match on the condition portion of the loop.
        //
        let (cmp_op, cmp_left, cmp_right) =
            match get_ref!(@func_ctx, self).func.expressions[loop_cond_handle] {
                crate::Expression::Binary { op, left, right } => Ok((op, left, right)),
                _ => Err(BoundsCheckError::UnsupportedLoopStructure),
            }?;

        let cmp_end = match (
            &get_ref!(@func_ctx, self).func.expressions[cmp_left],
            &get_ref!(@func_ctx, self).func.expressions[cmp_right],
        ) {
            (&crate::Expression::Load { ref pointer }, _) if *pointer == lvar_expr_handle => {
                Ok(cmp_right)
            }

            (_, &crate::Expression::Load { ref pointer }) if *pointer == lvar_expr_handle => {
                Ok(cmp_left)
            }
            _ => Err(BoundsCheckError::UnsupportedLoopStructure),
        }?;

        let cmp_op: abc_helper::CmpOp = cmp_op.try_into().map_err(|_| {
            BoundsCheckError::Unsupported(format!(
                "Unsupported comparison operator for loop condition {:?}",
                cmp_op
            ))
        })?;

        // Get the init as a Term.
        let init_expr = self.visit_expr(lvar_expr_handle)?;

        // Get the max as a term.
        let end_expr = self.visit_expr(cmp_end)?;

        // This is the term for the init...
        let init = get_ref!(@block_ctx, self).local_variable_map[&lvar_handle].clone();

        // We know start and end. Now we need to figure out how it is incremented, and make the term that it is incremented with.
        use crate::BinaryOperator as BinOp;
        if let crate::Expression::Binary { op, left, right } =
            get_ref!(@func_ctx, self).func.expressions[update_handle_expr]
        {
            // `other` is the side of the induction variable that is not the load to the induction variable.
            let other = match (
                &get_ref!(@func_ctx, self).func.expressions[left],
                &get_ref!(@func_ctx, self).func.expressions[right],
            ) {
                (&crate::Expression::Load { pointer }, other) if pointer == lvar_expr_handle => {
                    Ok(right)
                }

                (other, &crate::Expression::Load { pointer }) if pointer == lvar_expr_handle => {
                    Ok(left)
                }
                _ => Err(BoundsCheckError::UnsupportedLoopStructure),
            }?;

            // We make a term for the expression that we are incremented by.
            let inc_term = self.visit_expr(other)?;

            // And now, we make the increment term.

            // We need a new term that is being used as the increment.
            let next_term = self.mark_var(
                &get_ref!(@func_ctx, self).func.local_variables[lvar_handle].clone(),
                "local",
            )?;

            // Now, get the binary op
            let abc_op: abc_helper::BinaryOp = op.try_into().map_err(|_| {
                BoundsCheckError::Unsupported(format!(
                    "Unsupported binary operator for increment expression {:?}",
                    op
                ))
            })?;

            let old = self
                .current_block_ctx
                .as_mut()
                .expect("Block context should be initialized during visit")
                .local_variable_map
                .insert(lvar_handle, (next_term.clone(), true))
                .ok_or(BoundsCheckError::Unexpected(
                    "Undefined local variable".to_string(),
                ))?
                .0;

            // now we have to remove the old term from the expressions we have visited..
            {
                let Some(ref mut func_summary) = self.current_fn_summary else {
                    unreachable!("Function summary should be initialized during visit");
                };
                func_summary.expressions.remove(&lvar_expr_handle);
                func_summary.expressions.remove(&load_handle);
            }

            // Okay, now we `begin_loop`.
            // Here we assume an `increasing` loop that has been normalized.
            // e.g., starts at N, increases by one.
            self.helper
                .mark_loop_variable(&next_term, &old, &inc_term, abc_op)?;
            let loop_cond_term = self.visit_expr(loop_cond_handle)?;

            self.helper.begin_loop(&loop_cond_term)?;

            // Now, iterate through the rest of body.
            // First, though, get a snapshot of the block context.
            // Okay, we take the old ctx out of the current block ctx.
            let mut old_ctx = self
                .current_block_ctx
                .take()
                .expect("Block context should exist during visit");
            self.current_block_ctx = Some(old_ctx.reset_writes());
            // Safety: We just called unwrap on this same value.

            // Now, we iterate through the rest of the statements in the body..
            self.push_path_part(StatementPathPart::LoopBody);
            for stmt in body_iter {
                if let Statement::Emit(ref r) = *stmt {
                    self.visit_Emit(r)?;
                    continue;
                }
                self.push_path_part(StatementPathPart::Index(body_iter_idx));
                body_iter_idx += 1;

                self.visit_Statement(stmt)?;
                let was_terminator = self
                    .visitor_info
                    .statement_map
                    .get(&self.current_path)
                    .expect("visited block statement should exist in statement map")
                    .is_terminator();
                self.pop_path_part();
                // If this is a terminator, then we need to stop immediately.
                if was_terminator {
                    break;
                }
            }
            // pop the `LoopBody` path part.
            self.pop_path_part();

            self.helper.end_loop()?;
            let mut loop_ctx_map = self
                .current_block_ctx
                .take()
                .expect("Block ctx should still exist after visits.");

            // We need to update the variables that were modified in the loop here.
            self.update_loop(
                // Safety: We set this value to `Some` just above.
                &mut loop_ctx_map.local_variable_map,
                &mut old_ctx.local_variable_map,
                &loop_cond_term,
                &get_ref!(@func_ctx, self).func.local_variables.clone(),
                "local",
            )?;

            self.update_loop(
                &mut loop_ctx_map.global_variable_map,
                &mut old_ctx.global_variable_map,
                &loop_cond_term,
                &self.module_info.unwrap().module.global_variables,
                "global",
            )?;
            self.current_block_ctx = Some(old_ctx);

            // Now, after the loop, I have to mark each variable that was updated..
            // Now we have to unify the block context..
            // Though if the loop variable was written to, then this is an unsupported loop
            Ok(())
        } else {
            Err(BoundsCheckError::UnsupportedLoopStructure)
        }
    }
}

impl BoundsChecker<'_> {
    /// Gets the current function
    ///
    /// # Panics
    /// Panics if `self.module_info` is `None`
    fn get_current_function(&self) -> FunctionWithInfo {
        let mod_info = self
            .module_info
            .expect("Module info should be initialized during visit");

        match *self
            .current_path
            .first()
            .expect("Path should not be empty in visitors")
        {
            StatementPathPart::Function(ref f) => FunctionWithInfo {
                func: &mod_info.module.functions[*f],
                info: &mod_info.validation_info[*f],
                key: FnKey::Function(*f),
            },
            StatementPathPart::EntryPoint(ref ep_key @ EntryPointIndex(ref ep_idx)) => {
                FunctionWithInfo {
                    func: &mod_info.module.entry_points[*ep_idx].function,
                    info: mod_info.validation_info.get_entry_point(*ep_idx),
                    key: FnKey::EntryPoint(*ep_key),
                }
            }
            _ => unreachable!("Current path should be a function or entry point"),
        }
    }
}
