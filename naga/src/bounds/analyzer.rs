// SPDX-FileCopyrightText: 2024 University of Rochester
//
// SPDX-License-Identifier: MIT

// Interface for bounds checks.

// Right now, we have an interface that adds

// use super::BoundsInfo;

#![allow(dead_code, unused_variables, unused_imports)]

use std::{
    collections::HashMap,
    fmt::Debug,
    ops
};

use super::helper_interface::{self, HasName, HasType};

use crate::{
    arena::BadHandle, valid::ModuleInfo, ArraySize, FastHashMap, FunctionArgument, GlobalVariable,
    Module,
};
use abc_helper::{self, AbcExpression, AbcScalar, AbcType, ConstraintInterface, Predicate, Term};
use log::info as log_info;
use rustc_hash::FxHashMap;

/// Convenience struct used to pass around a module with its info together in one term.
#[derive(Clone, Copy)]
struct ModuleWithInfo<'a> {
    module: &'a Module,
    info: &'a ModuleInfo,
}

/// Convenience struct used to pass around a function with its info together in one term.
struct FunctionWithInfo<'a> {
    func: &'a crate::Function,
    info: &'a crate::valid::FunctionInfo,
}

/// Macro used only for debugging purposes that prints the variant of an expression.
#[allow(unused_macros)]
macro_rules! expression_variant {
    ($expr:expr) => {
        match $expr {
            crate::Expression::Literal { .. } => "Literal",
            crate::Expression::Constant { .. } => "Constant",
            crate::Expression::Override { .. } => "Override",
            crate::Expression::ZeroValue { .. } => "ZeroValue",
            crate::Expression::Compose { .. } => "Compose",
            crate::Expression::Access { .. } => "Access",
            crate::Expression::AccessIndex { .. } => "AccessIndex",
            crate::Expression::Splat { .. } => "Splat",
            crate::Expression::Swizzle { .. } => "Swizzle",
            crate::Expression::FunctionArgument(..) => "FunctionArgument",
            crate::Expression::GlobalVariable(..) => "GlobalVariable",
            crate::Expression::LocalVariable(..) => "LocalVariable",
            crate::Expression::Load { .. } => "Load",
            crate::Expression::ImageSample { .. } => "ImageSample",
            crate::Expression::ImageLoad { .. } => "ImageLoad",
            crate::Expression::ImageQuery { .. } => "ImageQuery",
            crate::Expression::Unary { .. } => "Unary",
            crate::Expression::Binary { .. } => "Binary",
            crate::Expression::Select { .. } => "Select",
            crate::Expression::Derivative { .. } => "Derivative",
            crate::Expression::Relational { .. } => "Relational",
            crate::Expression::Math { .. } => "Math",
            crate::Expression::As { .. } => "As",
            crate::Expression::CallResult { .. } => "CallResult",
            crate::Expression::AtomicResult { .. } => "AtomicResult",
            crate::Expression::WorkGroupUniformLoadResult { .. } => "WorkGroupUniformLoadResult",
            crate::Expression::ArrayLength(..) => "ArrayLength",
            crate::Expression::RayQueryProceedResult { .. } => "RayQueryProceedResult",
            crate::Expression::RayQueryGetIntersection { .. } => "RayQueryGetIntersection",
            crate::Expression::SubgroupBallotResult { .. } => "SubgroupBallotResult",
            crate::Expression::SubgroupOperationResult { .. } => "SubgroupOperationResult",
            // In case new expressions are added in the future...
            #[allow(unreachable_patterns)]
            _ => "UNKNOWN_EXPR_KIND",
        }
    };
}

/// Macro used only for debugging purposes that prints the variant of a statement.
#[allow(unused_macros)]
macro_rules! statement_variant {
    ($expr:expr) => {
        match $expr {
            crate::Statement::Emit { .. } => "Emit",
            crate::Statement::Block { .. } => "Block",
            crate::Statement::If { .. } => "If",
            crate::Statement::Switch { .. } => "Switch",
            crate::Statement::Loop { .. } => "Loop",
            crate::Statement::Break { .. } => "Break",
            crate::Statement::Continue { .. } => "Continue",
            crate::Statement::Return { .. } => "Return",
            crate::Statement::Kill { .. } => "Kill",
            crate::Statement::Barrier(..) => "Barrier",
            crate::Statement::Store { .. } => "Store",
            crate::Statement::ImageStore { .. } => "ImageStore",
            crate::Statement::Atomic { .. } => "ImageStore",
            crate::Statement::WorkGroupUniformLoad { .. } => "WorkGroupUniformLoad",
            crate::Statement::Call { .. } => "Call",
            crate::Statement::RayQuery { .. } => "RayQuery",
            crate::Statement::SubgroupBallot { .. } => "SubgroupBallot",
            crate::Statement::SubgroupGather { .. } => "SubgroupGather",
            crate::Statement::SubgroupCollectiveOperation { .. } => "SubgroupCollectiveOperation",
            // In case new expressions are added in the future...
            #[allow(unreachable_patterns)]
            _ => "UNKNOWN_STMT_KIND",
        }
    };
}

/// Type alias for the handle type used in the AbcHelper
type ConstraintHandle<T> = <abc_helper::ConstraintHelper as ConstraintInterface>::Handle<T>;

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
pub struct BoundsChecker {
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
}

impl ops::Index<crate::Handle<crate::Type>> for BoundsChecker {
    type Output = ConstraintHandle<AbcType>;
    fn index(&self, handle: crate::Handle<crate::Type>) -> &Self::Output {
        &self.types[handle.index()]
    }
}

impl ops::Index<crate::Handle<GlobalVariable>> for BoundsChecker {
    type Output = Term;
    fn index(&self, handle: crate::Handle<GlobalVariable>) -> &Self::Output {
        &self.global_vars[handle.index()]
    }
}

impl ops::Index<crate::Handle<crate::Function>> for BoundsChecker {
    type Output = FunctionSummary;
    fn index(&self, handle: crate::Handle<crate::Function>) -> &Self::Output {
        &self.functions[handle.index()]
    }
}

impl ops::IndexMut<crate::Handle<crate::Function>> for BoundsChecker {
    fn index_mut(&mut self, handle: crate::Handle<crate::Function>) -> &mut FunctionSummary {
        &mut self.functions[handle.index()]
    }
}

impl ops::Index<crate::Handle<crate::Expression>> for BoundsChecker {
    type Output = Term;
    fn index(&self, handle: crate::Handle<crate::Expression>) -> &Self::Output {
        &self.global_exprs[&handle]
    }
}

impl ops::Index<crate::Handle<crate::Override>> for BoundsChecker {
    type Output = Term;
    fn index(&self, handle: crate::Handle<crate::Override>) -> &Self::Output {
        &self.overrides[handle.index()]
    }
}

impl ops::Index<crate::Handle<crate::Constant>> for BoundsChecker {
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
    pub(self) expressions: FastHashMap<crate::Handle<crate::Expression>, Term>,
    pub(self) arguments: Vec<Term>,
    pub(self) local_variabes: Vec<Term>,
    pub(self) ret_ty: ConstraintHandle<AbcType>,
    nargs: u8,
}

/// Partial function summary is a function summary without a handle. The handle is added at the end.
impl PartialFunctionSummary {
    fn to_function_summary(self, handle: ConstraintHandle<abc_helper::Summary>) -> FunctionSummary {
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

impl ops::Index<crate::Handle<crate::LocalVariable>> for PartialFunctionSummary {
    type Output = Term;
    /// PartialFunctionSummary can be indexed by a local variable handle to get
    /// the helper's `Term` corresponding to the local variable.
    fn index(&self, handle: crate::Handle<crate::LocalVariable>) -> &Self::Output {
        &self.local_variabes[handle.index()]
    }
}

/// A function summary.
///
/// A function summary works as a bridge between the function in the module and the `Summary` in the helper.
///
/// It can be indexed by an [`Expression`] handle to get the helper's `Term` corresponding to the expression.
/// It can also be indexed by a [`LocalVariable`] handle to get the helper's `Term` corresponding to the local variable.
///
/// The `handle` field
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

impl ops::Index<crate::Handle<crate::LocalVariable>> for FunctionSummary {
    type Output = Term;
    fn index(&self, handle: crate::Handle<crate::LocalVariable>) -> &Self::Output {
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
        match self {
            ExpressionOrLiteral::Expression(e) => write!(f, "{}", e),
            ExpressionOrLiteral::Literal(l) => write!(f, "{}", l),
        }
    }
}

/// Helper to allow for generic funhctions of HasName

#[derive(Clone, Debug, thiserror::Error)]
pub enum BoundsCheckError {
    #[error("Bounds check failed: {0}")]
    BoundsCheckFailed(String),
    #[error("Unsupported: {0}")]
    Unsupported(String),
    #[error("{0}")]
    Unexpected(String),
    #[error("Attempt to reference a type that has not been declared.")]
    UndefinedType,
    #[error("{0}")]
    BadHandle(#[from] BadHandle),
    #[error("{0}")]
    ConstraintHelperError(#[from] abc_helper::ConstraintError),
}

enum ResolvedAccess {
    Struct(crate::Type),
    Array {
        inner: crate::TypeInner,
        dimension: usize,
    },
}

impl BoundsChecker {
    pub fn new() -> Self {
        BoundsChecker::default()
    }

    pub fn reset(&mut self) {
        self.functions.clear();
        self.global_vars.clear();
    }

    fn make_type(&mut self, ty: &crate::Type) -> Result<AbcType, BoundsCheckError> {
        use crate::TypeInner::*;
        // Wgsl doesn't allow self-referential types.
        // We also assume that any TypeInner in an arena refers to a type that is already defined in the arena.
        match ty.inner {
            Atomic(..) => Err(BoundsCheckError::Unsupported("Atomic type".to_string())),
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
            Scalar(s) => Ok(AbcType::Scalar(AbcScalar::from(s))),
            Vector { size, scalar } => Ok(AbcType::SizedArray {
                ty: AbcType::Scalar(scalar.into()).into(),
                size: size.into(),
            }),
            Struct { ref members, .. } => {
                // We make a struct type
                let mut my_map =
                    crate::FastHashMap::with_capacity_and_hasher(members.len(), Default::default());

                for member in members {
                    if member.binding.is_some() {
                        return Err(BoundsCheckError::Unsupported(
                            "Struct member with bindings".to_string(),
                        ));
                    }
                    let name = member.name.clone().ok_or(BoundsCheckError::Unsupported(
                        "Unnamed struct member".to_string(),
                    ))?;
                    my_map.insert(name, self.types[member.ty.index()].clone());
                }
                Ok(AbcType::Struct {
                    members: my_map.into(),
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
        handle: crate::Handle<T>,
        term: &T,
        space: &str,
    ) -> Result<Term, BoundsCheckError> {
        let varname = match term.to_name() {
            Some(name) => {
                // Make the var
                name.clone()
            }
            None => {
                let mut name = String::from("$anon_") + space;
                name.push_str(&handle.index().to_string());
                name
            }
        };
        let var = self
            .helper
            .declare_var(abc_helper::Var {
                name: varname.into(),
            })
            .map_err(|e| BoundsCheckError::ConstraintHelperError(e))?;

        // Mark the type of the variable
        let ty = self.types[term.to_type().index()].clone();
        self.helper
            .mark_type(var.clone(), ty)
            .map_err(|e| BoundsCheckError::ConstraintHelperError(e))?;

        Ok(var)
    }

    // Not sure if we need this...
    fn expr_to_string(
        &self,
        expr: crate::Handle<crate::Expression>,
        named: bool,
        module: &Module,
        mod_info: &ModuleInfo,
        func: &crate::Function,
    ) -> String {
        use crate::Expression;
        let built = String::new();
        // If the expression is in NamedExpressions, use that...
        if named {
            if let Some(named) = func.named_expressions.get(&expr) {
                return named.clone();
            }
        }
        let expr = &func.expressions[expr];

        match expr {
            Expression::Access { base, index } => {
                let base_str = self.expr_to_string(*base, true, module, mod_info, func);
                let index_str = self.expr_to_string(*index, true, module, mod_info, func);
                format!("{}[{}]", base_str, index_str)
            }
            Expression::FunctionArgument(idx) => {
                format!("@arg{}", idx)
            }
            _ => format!("{:?}", expr),
        }
    }

    /// Make a name for the expression.
    ///
    /// If the expression is named, then we use the next of said name.
    /// Otherwise, we use `$anon_expr_{index}``
    fn expr_to_name(
        &mut self,
        expr_handle: crate::Handle<crate::Expression>,
        func: &crate::Function,
    ) -> String {
        if let Some(name) = func.named_expressions.get(&expr_handle) {
            return self.next_var_name(name);
        }
        let mut name = String::from("$anon_expr_");
        name.push_str(&expr_handle.index().to_string());
        name
    }

    /// Get the next var name
    ///
    /// # Panics
    /// If the counter for the variable is greater than u32::Max
    fn next_var_name(&mut self, name: &String) -> String {
        let counter = self.unique_counter.entry(name.to_string()).or_insert(0);
        if *counter == 0 {
            return name.clone();
        } else if *counter == u32::MAX {
            panic!("Variable counter overflow");
        } else {
            // name = name${cntr}
            // We use `$`` to avoid having to worry about variables that already have _1 in them in the source code.
            // As `$` is not a valid wgsl identifier.
            *counter += 1;
            let mut s = String::with_capacity(name.len() + 2);
            s.push_str(name);
            s.push('$');
            s.push_str(&counter.to_string());
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
        module_info: &ModuleWithInfo,
        func_ctx: &FunctionWithInfo,
        // Give me the source code for the expression...
    ) -> Result<Term, BoundsCheckError> {
        use crate::proc::TypeResolution;
        let base_expr_info = &func_ctx.info[base_expr_handle].ty;
        let (naga_ty, ref abc_ty) = match base_expr_info {
            TypeResolution::Handle(ty) => (&module_info.module.types[*ty], self[*ty].clone()),
            TypeResolution::Value(crate::TypeInner::Pointer { base, space }) => {
                (&module_info.module.types[*base], self[*base].clone())
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

        match abc_ty.as_ref() {
            AbcType::SizedArray { size, .. } => {
                // Add the constraint that the index is less than the size
                let index_literal: Term = as_expression!(index);
                let size_literal: Term = Term::new_literal(*size);
                // Note: We can optimize this later on by reusing the same literal for 0.
                self.helper.add_tracked_constraint(
                    index_literal.clone(),
                    abc_helper::ConstraintOp::Cmp(abc_helper::CmpOp::Lt),
                    size_literal.clone(),
                    // The expression this comes from...
                    &format!("{}[{}]", base_expr, index),
                )?;
                self.helper.add_tracked_constraint(
                    index_literal.clone(),
                    abc_helper::ConstraintOp::Cmp(abc_helper::CmpOp::Geq),
                    Term::new_literal(0),
                    &format!("{}[{}]", base_expr, index),
                )?;
                // Make a new expression that is an access to the base and the index.
                Ok(Term::new_index_access(
                    base_expr.clone(),
                    index_literal.clone(),
                ))
            }
            AbcType::DynamicArray { ty } => {
                let index_literal: Term = as_expression!(index);
                let res = Term::new_index_access(base_expr.clone(), index_literal.clone());
                self.helper.add_tracked_constraint(
                    index_literal.clone(),
                    abc_helper::ConstraintOp::Cmp(abc_helper::CmpOp::Geq),
                    Term::new_literal(0),
                    &format!("{}[{}]", base_expr, &index),
                )?;
                // We need an expression for the array length..
                let len_expression = self
                    .helper
                    .add_expression(AbcExpression::ArrayLength(base_expr.clone()))?;
                self.helper.add_tracked_constraint(
                    index_literal.clone(),
                    abc_helper::ConstraintOp::Cmp(abc_helper::CmpOp::Lt),
                    // todo: fix this.
                    len_expression,
                    &format!("{}[{}]", base_expr, index),
                )?;
                Ok(res)
            }
            AbcType::Struct { members } => {
                if let ExpressionOrLiteral::Literal(l) = index {
                    Ok(Term::new_struct_access(
                        base_expr.clone(),
                        match &naga_ty.inner {
                            crate::TypeInner::Struct { members, .. } => {
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
            _ => {
                return Err(BoundsCheckError::Unsupported(format!(
                    "AccessIndex with {:?} as a base type.",
                    abc_ty
                )));
            }
        }
    }

    /// Visit an expression in a function, returning a handle to a variable that can be used to refer to the expression.
    ///
    /// If the expression has already been visited, then no work is done and we return the same handle as before.
    /// Otherwise, we visit all sub expressions therein.
    fn visit_expr(
        &mut self,
        module_info: &ModuleWithInfo,
        expr_handle: crate::Handle<crate::Expression>,
        func_ctx: &FunctionWithInfo,
        func_summary: &mut PartialFunctionSummary,
    ) -> Result<Term, BoundsCheckError> {
        // If the expression has already been visited, we just return a handle to it.
        if let Some(e) = func_summary.expressions.get(&expr_handle) {
            return Ok(e.clone());
        }
        // It's probably an error if we have an expression that is visited a second time in an Emit, right?
        // Because an emit would end up changing the scope...
        // As in, if we had a load(x) and then we saw emit, then the expressions therein need to be named.
        // Otherwise, we need to visit the expression.
        // We'll mark the type of the expression as we go.
        let expr = &func_ctx.func.expressions[expr_handle];
        log_info!("Visiting expression: {:?}", expr);

        // If the expression is named, then we use a var with that name and the result is an expression over said var.
        // After binding to a variable, we mark the expression's type.
        // This is nice because we can use the type of the expression from the arena?
        // Now we mark the type of this expression we just got
        // When we load an expression, we
        use crate::Expression as Expr;

        let expr_info = &func_ctx.info[expr_handle];

        let resolved: Term = match expr {
            Expr::Splat { size, value } => Term::new_splat(
                self.visit_expr(module_info, *value, func_ctx, func_summary)?,
                (*size).into(),
            ),
            // For right now, when we see load, we should just return the variable bound to the inner...
            // Although, for 'store', this really needs to mark the current variable name...
            // A 'load' should get the most recent variable name of the expression it is loading from...
            Expr::Load { pointer } => {
                // We will make a new expression holding the value of the thing being loaded from...
                self.visit_expr(module_info, *pointer, func_ctx, func_summary)?
                // When we load, we should use the last SSA variable name.
            }
            Expr::Literal(lit) => Term::new_literal(lit.to_string()),
            Expr::Constant(c) => self[*c].clone(),
            Expr::Override(o) => self[*o].clone(),
            Expr::FunctionArgument(idx) => func_summary.arguments[*idx as usize].clone(),
            Expr::Binary { op, left, right } => {
                let left = self.visit_expr(module_info, *left, func_ctx, func_summary)?;
                let right = self.visit_expr(module_info, *right, func_ctx, func_summary)?;
                Self::binary_to_abc_expression(*op, left, right)?
            }
            Expr::Access { base, index, .. } => {
                let new_base = self.visit_expr(module_info, *base, func_ctx, func_summary)?;
                let new_index = self.visit_expr(module_info, *index, func_ctx, func_summary)?;
                self.make_access(
                    *base,
                    new_base,
                    ExpressionOrLiteral::Expression(new_index),
                    module_info,
                    func_ctx,
                )?
            }
            // We should mark the type of the pointer
            // Expr::FunctionArgument(idx) => func_ctx.arguments[*idx as usize].clone(),
            Expr::AccessIndex { base, index } => {
                let new_base = self.visit_expr(module_info, *base, func_ctx, func_summary)?;
                self.make_access(
                    *base,
                    new_base,
                    ExpressionOrLiteral::Literal(*index),
                    module_info,
                    func_ctx,
                )?
            }
            Expr::As {
                expr: a,
                kind: s,
                convert: b,
            } => {
                let a = self.visit_expr(module_info, *a, func_ctx, func_summary)?;
                use crate::ScalarKind;
                match (s, b) {
                    (ScalarKind::Sint, Some(b)) => {
                        Term::new_cast(a.clone(), abc_helper::AbcScalar::Sint(*b))
                    }
                    (ScalarKind::Uint, Some(b)) => {
                        Term::new_cast(a.clone(), abc_helper::AbcScalar::Uint(*b))
                    }
                    (ScalarKind::Float, Some(b)) => {
                        Term::new_cast(a.clone(), abc_helper::AbcScalar::Float(*b))
                    }
                    (ScalarKind::Bool, _) => Term::new_unit_pred(a),
                    _ => {
                        return Err(BoundsCheckError::Unsupported(format!(
                            "Cast of type {:?} of size {:?}",
                            s, b
                        )));
                    }
                }
            }
            Expr::GlobalVariable(g) => self[*g].clone(),
            Expr::LocalVariable(l) => func_summary[*l].clone(),
            Expr::CallResult(c) => {
                return Err(BoundsCheckError::Unexpected(
                    "Attempted to visit a call result.".to_string(),
                ))
            }
            _ => {
                return Err(BoundsCheckError::Unsupported(
                    "Unsupported expression type: ".to_owned() + expression_variant!(expr),
                ));
            }
        };

        // If this is a named expression, then we use the name to refer to said expression.
        // Otherwise, the result is the term we evaluated.
        let resolved =
            if let Some(named_expression) = func_ctx.func.named_expressions.get(&expr_handle) {
                let varname = self.next_var_name(named_expression);
                let expr_var_name = self.helper.declare_var(abc_helper::Var { name: varname })?;

                // Add the equality constraint.
                self.helper.add_constraint(
                    expr_var_name.clone(),
                    abc_helper::ConstraintOp::Assign,
                    resolved.into(),
                )?;

                // TODO: Figure out if we need to mark the type of the expression?
                // We shouldn't need to do this, right?
                // let info = &func_ctx.info[expr_handle];

                expr_var_name
                // AbcExpression::new_var(var)
            } else {
                resolved
            };
        func_summary
            .expressions
            .insert(expr_handle, resolved.clone());

        Ok(resolved)

        // #[allow(unreachable_code)]
        // Ok(())
    }

    fn visit_statement(
        &mut self,
        stmt: &crate::Statement,
        module: &ModuleWithInfo,
        func_ctx: &FunctionWithInfo,
        func_summary: &mut PartialFunctionSummary,
        block_ctx: Option<&crate::Block>,
    ) -> Result<bool, BoundsCheckError> {
        use crate::Statement;
        match stmt {
            Statement::Loop {
                body,
                continuing,
                break_if,
            } => {
                if break_if.is_some() {
                    return Err(BoundsCheckError::Unsupported(
                        "Loop with a non empty break_if".to_string(),
                    ));
                }
                if body.len() == 0 {
                    return Err(BoundsCheckError::Unsupported(
                        "Loop with an empty body".to_string(),
                    ));
                }
                // we want an iterator over body
                let mut body_iter = body.into_iter().peekable();
                // Go through all of the emits.

                while let Some(Statement::Emit(ref r)) = body_iter.peek() {
                    // iterate through the expressions in r
                    for e in r.clone().into_iter() {
                        self.visit_expr(module, e, func_ctx, func_summary)?;
                    }
                    body_iter.next();
                }
                // We expect to see an If (condition) { {}; break; } structure.
                // This indicates that this is a traditional loop.
                // Otherwise, this is the `do-while` loop form that, well, we just don't
                match body_iter.next() {
                    Some(Statement::If {
                        condition,
                        accept,
                        reject,
                    }) if matches!(reject.get(0), Some(Statement::Break)) && accept.len() == 0 => {
                        // Accept must be of len 1 with a single statement that is a break.
                        let condition =
                            self.visit_expr(module, *condition, func_ctx, func_summary)?;
                        self.helper.begin_loop(condition)?;
                    },
                    Some(s) => 
                        return Err(BoundsCheckError::Unsupported(
                            format!(
                                "Unsupported loop structure, expecting If have {}", statement_variant!(s)
                            )
                        )),
                    None => {
                        return Err(BoundsCheckError::Unsupported(
                            "Loop with an empty body".to_string(),
                        ));
                    }
                }
                // Now that we have gotten the loop structure out of the way, we can visit the rest of the statements.
                for smt in body_iter {
                    self.visit_statement(smt, module, func_ctx, func_summary, block_ctx)?;
                }
                for stmt in continuing {
                    self.visit_statement(stmt, module, func_ctx, func_summary, block_ctx)?;
                }

            }
            Statement::Emit(ref r) => {
                for e in r.clone().into_iter() {
                    self.visit_expr(module, e, func_ctx, func_summary)?;
                }
            }
            Statement::Call {
                function,
                arguments,
                result,
            } => {
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
                for arg in arguments {
                    let arg = self.visit_expr(module, *arg, func_ctx, func_summary)?;
                    args.push(arg);
                }

                let res_into = if let Some(result) = result {
                    // If there is a result, we store the handle to expression that lets us refer to it.
                    let result_name = self.expr_to_name(*result, func_ctx.func);
                    let var = self
                        .helper
                        .declare_var(abc_helper::Var { name: result_name })?;
                    func_summary
                        .expressions
                        .insert(*result, self.helper.make_call(handle, args, Some(var))?);
                } else {
                    // If there is no result, we just make the call.
                    self.helper.make_call(handle, args, None)?;
                };

                // Then we add a constraint tht the result equals the call.
            }
            Statement::Return { value: Some(v) } => {
                // Visit the containing expression.
                let expr = self.visit_expr(module, *v, func_ctx, func_summary)?;
                // These variables were assigned to in the block.
                self.helper.mark_return(Some(expr))?;
                return Ok(false);
            }
            Statement::Return { value: None } => {
                self.helper.mark_return(None)?;
                // When we get to a return, we stop processing all statements in the block.
                return Ok(false);
            }
            Statement::Break => {
                // If the block context is a loop, then we immediately stop processing more elements in the block.
                self.helper.mark_break()?;
                return Ok(false);
            }
            Statement::Continue => {
                self.helper.mark_continue()?;
                return Ok(false);
            }
            Statement::If {
                condition,
                accept,
                reject,
            } => {
                let condition = self.visit_expr(module, *condition, func_ctx, func_summary)?;
                if accept.len() > 0 {
                    self.helper.begin_predicate_block(condition.clone())?;
                    self.visit_block(accept, module, func_ctx, func_summary, block_ctx)?;
                    self.helper.end_predicate_block()?;
                }
                if reject.len() > 0 {
                    self.helper
                        .begin_predicate_block(Term::new_not(condition))?;
                    self.visit_block(reject, module, func_ctx, func_summary, block_ctx)?;
                    self.helper.end_predicate_block()?;
                }
            }
            Statement::Store { pointer, value } => {
                // If whatever expression we are storing to has a name, then we use that name.
                // When we see a store, we actually mark the term that we loaded from with the next name.
                let pointer = self.visit_expr(module, *pointer, func_ctx, func_summary)?;
                let value = self.visit_expr(module, *value, func_ctx, func_summary)?;
                // TODO: Figure out if we need to increment the identifer for the pointer.
                self.helper
                    .add_constraint(pointer, abc_helper::ConstraintOp::Assign, value)?;
            }
            Statement::Block(ref b) => {
                self.visit_block(b, module, func_ctx, func_summary, block_ctx)?
            }
            _ => {
                return Err(BoundsCheckError::Unsupported(
                    "Unsupported statement type: ".to_owned() + statement_variant!(stmt),
                ));
            }
        }
        Ok(true)
    }

    fn visit_block(
        &mut self,
        block: &crate::Block,
        module: &ModuleWithInfo,
        func_ctx: &FunctionWithInfo,
        func_summary: &mut PartialFunctionSummary,
        block_ctx: Option<&crate::Block>,
    ) -> Result<(), BoundsCheckError> {
        use crate::Statement;
        // Function info...
        for stmt in block.iter() {
            // If visit_statement returns false, that means we hit control flow and should stop processing more
            // elements in the block (e.g, we hit a `break`/`return`/`continue`).
            if ! self.visit_statement(stmt, module, func_ctx, func_summary, Some(block))? {
                break;
            }
        }

        Ok(())
    }

    fn check_function(
        &mut self,
        module: &ModuleWithInfo,
        func: &FunctionWithInfo,
        func_summary: &mut PartialFunctionSummary,
        name: &String,
    ) -> Result<(), BoundsCheckError> {
        let func_info = func.info;
        // Exit early if the function can kill, as this isn't supported.
        if func_info.may_kill {
            return Err(BoundsCheckError::Unsupported(
                "Functions that can kill invocations.".to_string(),
            ));
        }

        for (var_handle, var) in func.func.local_variables.iter() {
            let var = self.mark_var(var_handle, var, name)?;
            func_summary.local_variabes.push(var);
        }

        // begin the summary.
        if let Some(crate::FunctionResult { ty, .. }) = func.func.result {
            let ty = self[ty].clone();
            self.helper.mark_return_type(ty)?;
        }

        self.visit_block(&func.func.body, module, func, func_summary, None)?;

        // End the summary

        Ok(())
    }

    // pub fn mark_type(&mut self, ty: &crate::Type) {
    //     // We need to have a name for the types that we see.
    //     let ty_name = ty.name.clone().unwrap_or(String::from("$anon_type_"));
    //     let ty = abc_helper::Type { name: ty_name };
    //     self.helper.add_type(ty);
    // }

    // We need a handle of types to their names...

    // Converts a binary operator to an ABC expression
    fn binary_to_abc_expression(
        op: crate::BinaryOperator,
        lhs: Term,
        rhs: Term,
    ) -> Result<Term, BoundsCheckError> {
        use crate::BinaryOperator;
        use abc_helper::BinaryOp;
        use abc_helper::CmpOp;
        use abc_helper::Predicate;
        if let Some(binop) = op.try_into().ok() {
            Ok(Term::new_binary_op(binop, lhs, rhs))
        } else if let Some(cmpop) = op.try_into().ok() {
            Ok(Term::new_comparison(cmpop, lhs, rhs))
        } else {
            match op {
                BinaryOperator::LogicalAnd => Ok(Term::new_logical_and(lhs, rhs)),
                BinaryOperator::LogicalOr => Ok(Term::new_logical_or(lhs, rhs)),
                _ => Err(BoundsCheckError::Unsupported(
                    "Unsupported binary operator".to_string(),
                )),
            }
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
        let res: Term = match expr {
            Expr::Literal(t) => Term::new_literal(format!("{t}")),
            Expr::Constant(c) => self[*c].clone(),
            Expr::Binary { op, left, right } => {
                let left = self.global_expression_resolution(*left, module)?;
                let right = self.global_expression_resolution(*right, module)?;
                Self::binary_to_abc_expression(*op, left, right)?
                // A binary op with a boolean result maps to a predicate
                // Otherwise, it maps to a binary op.
            }
            _ => {
                let msg = String::from("Unsupported global expression type: ")
                    + format!("{:?}", expression_variant!(expr)).as_str();
                return Err(BoundsCheckError::Unsupported(msg));
            }
        }
        .into();
        self.global_exprs.insert(expr_handle, res.clone());
        Ok(res)
    }

    #[inline]
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
            .add_argument(name, self.types[arg.to_type().index()].clone())?;
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
    pub fn abc_impl(&mut self, module: &Module, info: &ModuleInfo) -> Result<(), BoundsCheckError> {
        // to begin with, mark types...

        // Clear the types...
        self.types = Vec::with_capacity(module.types.len());
        for (ty_handle, ty) in module.types.iter() {
            let ty = self.make_type(ty)?;
            self.types.push(ty.into());
        }

        // Now, mark the global expressions

        self.constants = Vec::with_capacity(module.constants.len());
        for (var_handle, var) in module.constants.iter() {
            let cnst = self.mark_var(var_handle, var, "glbl")?;
            self.constants.push(cnst.clone());
            // Push the initialization of the constant as a constraint.
            // Any expressions here can only refer to previously defined constants, right?

            // Resolve the initialization to an expression handle
            let expr =
                self.global_expression_resolution(var.init, &ModuleWithInfo { module, info })?;

            // Mark the constraint of the initialization.
            self.helper
                .add_constraint(cnst, abc_helper::ConstraintOp::Assign, expr)?;
        }
        self.overrides = Vec::with_capacity(module.overrides.len());
        for (var_handle, var) in module.overrides.iter() {
            let ovr = self.mark_var(var_handle, var, "glbl")?;
            self.overrides.push(ovr);
        }

        for (var_handle, var) in module.global_variables.iter() {
            let var = self.mark_var(var_handle, var, "glbl")?;
            self.global_vars.push(var);
        }

        for (fun_handle, fun) in module.functions.iter() {
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

            let mut finfo = FunctionWithInfo {
                func: fun,
                info: &info[fun_handle],
            };

            // Begin the summary

            // Add the function arguments
            // This is done outside of the `check_function` method because
            // entry points do something special with their arguments.

            // Now begin the common function handling logic
            self.check_function(
                &ModuleWithInfo { module, info },
                &mut finfo,
                &mut partial_summary,
                &func_name,
            )?;
            let summary_handle = self.helper.end_summary()?;
            self.functions
                .push(partial_summary.to_function_summary(summary_handle));
        }

        // Entry points contain function summaries.
        for (pos, ep) in module.entry_points.iter().enumerate() {
            log_info!("Checking entry point: {}", ep.name);
            // An entry
            let func_name = ep.name.clone();
            let mut partial_summary = self.make_function_summary(&ep.function)?;
            let nargs = partial_summary.nargs;
            self.helper.begin_summary(func_name.clone(), nargs)?;
            let ep_info = info.get_entry_point(pos);
            let mut finfo = FunctionWithInfo {
                func: &ep.function,
                info: &ep_info,
            };
            for (pos, arg) in ep.function.arguments.iter().enumerate() {
                let var = self.make_arg(arg, &ep.function, pos)?;
                // This arg *must* be a bound.
                use crate::Binding;
                match arg.binding {
                    Some(Binding::BuiltIn(crate::BuiltIn::LocalInvocationId)) => {
                        // If this is a local invocation id, then we add the constraint on its range from the workgroup information
                        // that we already have.
                        for (dim, high) in ep.workgroup_size.iter().enumerate() {
                            // make a term for the access to the 0th element of the expression.
                            let access_term =
                                Term::new_index_access(var.clone(), Term::new_literal(dim));
                            self.helper.mark_range(access_term, 0u32, *high - 1)?;
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
                partial_summary.arguments.push(var);
            }
            // For entry points, we need to make a new summary.

            self.check_function(
                &ModuleWithInfo { module, info },
                &mut finfo,
                &mut partial_summary,
                &func_name,
            )?;

            let summary_handle = self.helper.end_summary()?;
            // End the summary
            self.entry_points
                .push(partial_summary.to_function_summary(summary_handle));
        }

        Ok(())
    }
}
