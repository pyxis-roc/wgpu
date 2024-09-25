// SPDX-FileCopyrightText: 2024 University of Rochester
//
// SPDX-License-Identifier: MIT

// Interface for bounds checks.

// Right now, we have an interface that adds

// use super::BoundsInfo;

#![allow(dead_code, unused_variables, unused_imports)]

use std::{collections::HashMap, fmt::Debug, ops};

use super::helper_interface::{self, HasName, HasType};

use crate::{arena::BadHandle, valid::ModuleInfo, ArraySize, FastHashMap, GlobalVariable, Module};
use abc_helper::{self, AbcExpression, AbcScalar, AbcType, ConstraintInterface};
use log::{info, warn};
use rustc_hash::FxHashMap;
/// We need a cache for expressions that we have already transformed into naga expressions...

// impl crate::Expression {
//     fn to_abc_expression(self, ExprArena: crate::Arena<crate::Expression>, GlobalArena: crate::Arena<GlobalVariable>) {
//         match
//     }
// }

// // We can't actually do this because expressions refer to handles!!
// impl From<crate::Expression> for AbcExpression {
//     fn from(value: crate::Expression) -> Self {
//         match value {
//             crate::Expression::Access { base, index } =>
//         }
//     }
// }

// helper macros...
// Helper struct for passing around module info

#[derive(Clone, Copy)]
struct ModuleWithInfo<'a> {
    module: &'a Module,
    info: &'a ModuleInfo,
}

// impl From<(Module, ModuleInfo)> for ModuleWithInfo<'_> {
//     fn from((module, info): (Module, ModuleInfo)) -> Self {
//         ModuleWithInfo {
//             module: &module,
//             info: &info,
//         }
//     }
// }

/// Just a helper struct to simplify passing around functions with their info.
struct FunctionWithInfo<'a> {
    handle: crate::Handle<crate::Function>,
    func: &'a crate::Function,
    info: &'a crate::valid::FunctionInfo,
}

struct ExpressionWithInfo<'a> {
    handle: crate::Handle<crate::Expression>,
    expr: &'a crate::Expression,
    info: &'a crate::valid::ExpressionInfo,
}

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
// Simplify the type of a handle

type ConstraintHandle<T> = <abc_helper::ConstraintHelper as ConstraintInterface>::Handle<T>;

#[derive(Default)]
pub struct BoundsChecker {
    // Arena of vars we have...
    pub helper: abc_helper::ConstraintHelper,
    pub global_vars: Vec<ConstraintHandle<abc_helper::Var>>,
    // Global expressions for the main module...
    pub global_exprs:
        FastHashMap<crate::Handle<crate::Expression>, ConstraintHandle<AbcExpression>>,
    // Functions in the scope...
    pub functions: Vec<FunctionSummary>,

    pub entry_points: Vec<FunctionSummary>,
    /// Used to get the expression representing an override
    pub overrides: Vec<ConstraintHandle<abc_helper::Var>>,
    /// Used to get the expression representing a constant
    pub constants: Vec<ConstraintHandle<abc_helper::Var>>,
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
    type Output = ConstraintHandle<abc_helper::Var>;
    fn index(&self, handle: crate::Handle<GlobalVariable>) -> &ConstraintHandle<abc_helper::Var> {
        &self.global_vars[handle.index()]
    }
}

impl ops::Index<crate::Handle<crate::Function>> for BoundsChecker {
    type Output = FunctionSummary;
    fn index(&self, handle: crate::Handle<crate::Function>) -> &FunctionSummary {
        &self.functions[handle.index()]
    }
}

impl ops::IndexMut<crate::Handle<crate::Function>> for BoundsChecker {
    fn index_mut(&mut self, handle: crate::Handle<crate::Function>) -> &mut FunctionSummary {
        &mut self.functions[handle.index()]
    }
}

impl ops::Index<crate::Handle<crate::Expression>> for BoundsChecker {
    type Output = ConstraintHandle<AbcExpression>;
    fn index(&self, handle: crate::Handle<crate::Expression>) -> &Self::Output {
        &self.global_exprs[&handle]
    }
}

impl ops::Index<crate::Handle<crate::Override>> for BoundsChecker {
    type Output = ConstraintHandle<abc_helper::Var>;
    fn index(&self, handle: crate::Handle<crate::Override>) -> &Self::Output {
        &self.overrides[handle.index()]
    }
}

impl ops::Index<crate::Handle<crate::Constant>> for BoundsChecker {
    type Output = ConstraintHandle<abc_helper::Var>;
    fn index(&self, handle: crate::Handle<crate::Constant>) -> &Self::Output {
        &self.constants[handle.index()]
    }
}

struct PartialFunctionSummary {
    // Map from expression handles in the function to Expressions in the helper.
    // Expressions are always assigned to variables, so this actually maps to the handle of that variable.
    pub expressions: FastHashMap<crate::Handle<crate::Expression>, ConstraintHandle<AbcExpression>>,
    pub arguments: Vec<ConstraintHandle<abc_helper::Var>>,
    pub local_variabes: Vec<ConstraintHandle<abc_helper::Var>>,
    pub ret_ty: ConstraintHandle<AbcType>,
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
    type Output = ConstraintHandle<AbcExpression>;
    fn index(&self, handle: crate::Handle<crate::Expression>) -> &Self::Output {
        &self.expressions[&handle]
    }
}

impl ops::Index<crate::Handle<crate::LocalVariable>> for PartialFunctionSummary {
    type Output = ConstraintHandle<abc_helper::Var>;
    fn index(&self, handle: crate::Handle<crate::LocalVariable>) -> &Self::Output {
        &self.local_variabes[handle.index()]
    }
}

/// A function summary.
///
/// All fields are public because privatizing them limits the ability for other libraries
/// to interact with these.
pub struct FunctionSummary {
    pub expressions: FastHashMap<crate::Handle<crate::Expression>, ConstraintHandle<AbcExpression>>,
    pub arguments: Vec<ConstraintHandle<abc_helper::Var>>,
    pub local_variabes: Vec<ConstraintHandle<abc_helper::Var>>,
    pub handle: ConstraintHandle<abc_helper::Summary>,
    pub ret_ty: ConstraintHandle<AbcType>,
}

impl From<FunctionSummary> for PartialFunctionSummary {
    fn from(value: FunctionSummary) -> Self {
        PartialFunctionSummary {
            expressions: value.expressions,
            arguments: value.arguments,
            local_variabes: value.local_variabes,
            ret_ty: value.ret_ty,
        }
    }
}
impl ops::Index<crate::Handle<crate::Expression>> for FunctionSummary {
    type Output = ConstraintHandle<AbcExpression>;
    fn index(&self, handle: crate::Handle<crate::Expression>) -> &Self::Output {
        &self.expressions[&handle]
    }
}

impl ops::Index<crate::Handle<crate::LocalVariable>> for FunctionSummary {
    type Output = ConstraintHandle<abc_helper::Var>;
    fn index(&self, handle: crate::Handle<crate::LocalVariable>) -> &Self::Output {
        &self.local_variabes[handle.index()]
    }
}

#[derive(Debug, Clone)]
/// Either holds a u32 or a handle to an expression.
enum ExpressionOrLiteral {
    Expression(ConstraintHandle<AbcExpression>),
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
                size: match size {
                    crate::VectorSize::Quad => unsafe { std::num::NonZeroU32::new_unchecked(4) },
                    crate::VectorSize::Tri => unsafe { std::num::NonZeroU32::new_unchecked(3) },
                    crate::VectorSize::Bi => unsafe { std::num::NonZeroU32::new_unchecked(2) },
                    // future proofing for more vector sizes.
                    #[allow(unreachable_patterns)]
                    _ => {
                        return Err(BoundsCheckError::Unsupported(
                            "Unsupported vector size".to_string(),
                        ));
                    }
                },
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
    ) -> Result<ConstraintHandle<abc_helper::Var>, BoundsCheckError> {
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

    fn expr_to_abc_expr(
        &self,
        expr_handle: crate::Handle<crate::Expression>,
        module: &Module,
        mod_info: &ModuleInfo,
        func: &crate::Function,
        func_checker: &mut FunctionSummary,
    ) -> Result<ConstraintHandle<AbcExpression>, BoundsCheckError> {
        // Any expression referenced here must already be in our handle..
        let expr = &func.expressions[expr_handle];
        use crate::Expression as Expr;
        use AbcExpression as ABCExpr;
        Ok(match expr {
            Expr::Literal(t) => ABCExpr::Literal(format!("{t:?}")),
            Expr::Constant(c) => ABCExpr::Var(self[*c].clone()),
            Expr::Override(c) => ABCExpr::Var(self[*c].clone()),
            Expr::FunctionArgument(idx) => {
                ABCExpr::Var(func_checker.arguments[*idx as usize].clone())
            }
            _ => {
                let msg =
                    String::from("Unsupported expression type: ") + format!("{:?}", expr).as_str();
                return Err(BoundsCheckError::Unsupported(msg));
            }
        }
        .into())
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

    /// Gets the name of the function.
    ///
    /// If the function's name is None, then the name is $unnamed_func_{index}
    fn func_to_name(&self, module: &Module, func: crate::Handle<crate::Function>) -> String {
        if let Some(name) = module.functions[func].name.as_ref() {
            return name.clone();
        }
        let mut name = String::from("$anon_func_");
        name.push_str(&func.index().to_string());
        name
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
        base_expr: ConstraintHandle<AbcExpression>,
        index: ExpressionOrLiteral,
        module_info: &ModuleWithInfo,
        func_ctx: &FunctionWithInfo,
        // Give me the source code for the expression...
    ) -> Result<AbcExpression, BoundsCheckError> {
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
                    ExpressionOrLiteral::Literal(l) => {
                        self.helper.add_expression(AbcExpression::new_literal(l))?
                    }
                }
            };
        }

        match abc_ty.as_ref() {
            AbcType::SizedArray { size, .. } => {
                // Add the constraint that the index is less than the size
                let index_literal: ConstraintHandle<AbcExpression> = as_expression!(index);
                let size_literal: ConstraintHandle<AbcExpression> = self
                    .helper
                    .add_expression(AbcExpression::new_literal(*size))?;
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
                    AbcExpression::new_literal(0).into(),
                    &format!("{}[{}]", base_expr, index),
                )?;
                // Make a new expression that is an access to the base and the index.
                Ok(AbcExpression::new_index_access(
                    base_expr.clone(),
                    index_literal.clone(),
                ))
            }
            AbcType::DynamicArray { ty } => {
                let index_literal: ConstraintHandle<AbcExpression> = as_expression!(index);
                let res = AbcExpression::new_index_access(base_expr.clone(), index_literal.clone());
                self.helper.add_tracked_constraint(
                    index_literal.clone(),
                    abc_helper::ConstraintOp::Cmp(abc_helper::CmpOp::Geq),
                    AbcExpression::new_literal(0).into(),
                    &format!("{}[{}]", base_expr, &index),
                )?;
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
                    Ok(AbcExpression::new_struct_access(
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

    /// Given the TypeResolution for an access index, return the type that is being indexed into, along with its dimension, when this is
    /// a nested access.
    /// If it is a struct, then we return the type of that struct

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
    ) -> Result<ConstraintHandle<AbcExpression>, BoundsCheckError> {
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
        info!("Visiting expression: {:?}", expr);

        // If the expression is named, then we use a var with that name and the result is an expression over said var.
        // After binding to a variable, we mark the expression's type.
        // This is nice because we can use the type of the expression from the arena?
        // Now we mark the type of this expression we just got
        // When we load an expression, we
        use crate::Expression as Expr;

        let expr_info = &func_ctx.info[expr_handle];

        let resolved = match expr {
            Expr::Literal(lit) => AbcExpression::new_literal(lit.to_string()),
            Expr::Constant(c) => self[*c].clone().into(),
            Expr::Override(o) => self[*o].clone().into(),
            // For right now, when we see load, we should just return the variable bound to the inner...
            // Although, for 'store', this really needs to mark the current variable name...
            // A 'load' should get the most recent variable name of the expression it is loading from...
            Expr::Load { pointer } => {
                info!("Load expression: {:?}", func_ctx.func.expressions[*pointer]);
                // We will make a new expression holding the value of the thing being loaded from...
                let loaded = self.visit_expr(module_info, *pointer, func_ctx, func_summary);
                AbcExpression::new_var(abc_helper::Var {
                    name: self.expr_to_name(*pointer, func_ctx.func),
                })
                // When we load, we should use the last SSA variable name.
            }
            Expr::FunctionArgument(idx) => {
                let var = func_summary.arguments[*idx as usize].clone();
                AbcExpression::new_var(var)
            }
            Expr::Binary { op, left, right } => {
                let left = self.visit_expr(module_info, *left, func_ctx, func_summary)?;
                let right = self.visit_expr(module_info, *right, func_ctx, func_summary)?;
                if let Ok(op) = abc_helper::BinaryOp::try_from(*op) {
                    AbcExpression::new_binary_op(op, left, right)
                } else if let Ok(op) = abc_helper::CmpOp::try_from(*op) {
                    AbcExpression::new_cmp_op(op, left, right)
                } else {
                    return Err(BoundsCheckError::Unsupported(format!(
                        "Unsupported binary operation: {:?}",
                        op
                    )))?;
                }
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
                convert: Some(_), ..
            } => {
                return Err(BoundsCheckError::Unsupported(
                    "As expr with none none convert".to_string(),
                ))
            }
            Expr::As {
                expr: a, kind: s, ..
            } => {
                let a = self.visit_expr(module_info, *a, func_ctx, func_summary)?;
                return Err(BoundsCheckError::Unsupported(
                    r#""As" expressions"#.to_string(),
                ));
            }
            Expr::GlobalVariable(g) => {
                // Get the last ssa counter for the global variable reference?
                // No, honestly, we probably need to mark this.
                // Use the last counter for the global variable...
                self[*g].clone().into()
            }
            Expr::LocalVariable(l) => {
                let var = func_summary[*l].clone();
                AbcExpression::new_var(var)
            }
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

        // If this is a named expression, place it into a variable.
        if let Some(named_expression) = func_ctx.func.named_expressions.get(&expr_handle) {
            let varname = self.next_var_name(named_expression);
            let expr_as_var = self.helper.declare_var(abc_helper::Var { name: varname })?;
            // make the expression.
            let new_expr: ConstraintHandle<AbcExpression> = self
                .helper
                .add_expression(AbcExpression::new_var(expr_as_var.clone()))?;

            // Add the equality constraint.
            self.helper.add_constraint(
                new_expr.clone(),
                abc_helper::ConstraintOp::Assign,
                resolved.into(),
            )?;

            // Maybe we should resolve the type?
            let info = &func_ctx.info[expr_handle];

            // Add the expression to the function context.
            func_summary
                .expressions
                .insert(expr_handle, new_expr.clone());

            Ok(new_expr)
            // AbcExpression::new_var(var)
        } else {
            let resolved: ConstraintHandle<AbcExpression> = resolved.into();
            func_summary
                .expressions
                .insert(expr_handle, resolved.clone());
            Ok(resolved)
        }
        // #[allow(unreachable_code)]
        // Ok(())
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
            match stmt {
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
                    let called_func = self.functions.get(function.index()).ok_or(
                        BoundsCheckError::Unexpected(
                            "Reference to a function that has not been declared.".to_string(),
                        ),
                    )?;
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
                }
                Statement::Return { value: None } => {
                    self.helper.mark_return(None)?;
                    // When we get to a return, we stop processing all statements in the block.
                    return Ok(());
                }
                Statement::If {
                    condition,
                    accept,
                    reject,
                } => {
                    let condition = self.visit_expr(module, *condition, func_ctx, func_summary)?;
                    if accept.len() > 0 {
                        self.helper.begin_predicate_block(
                            abc_helper::Predicate::from_expression_handle(condition.clone()),
                        )?;
                        self.visit_block(accept, module, func_ctx, func_summary, Some(block))?;
                        self.helper.end_predicate_block()?;
                    }
                    if reject.len() > 0 {
                        self.helper
                            .begin_predicate_block(abc_helper::Predicate::new_not(
                                abc_helper::Predicate::from_expression_handle(condition.clone()),
                            ))?;
                        self.visit_block(reject, module, func_ctx, func_summary, Some(block))?;
                        self.helper.end_predicate_block()?;
                    }
                }
                Statement::Store { pointer, value } => {
                    let pointer = self.visit_expr(module, *pointer, func_ctx, func_summary)?;
                    let value = self.visit_expr(module, *value, func_ctx, func_summary)?;
                    // TODO: Figure out if we need to increment the identifer for the pointer.
                    self.helper
                        .add_constraint(pointer, abc_helper::ConstraintOp::Assign, value)?;
                }
                Statement::Block(ref b) => {
                    self.visit_block(b, module, func_ctx, func_summary, Some(block))?
                }
                _ => {
                    return Err(BoundsCheckError::Unsupported(
                        "Unsupported statement type: ".to_owned() + statement_variant!(stmt),
                    ));
                }
            }
        }

        Ok(())
    }

    fn check_function(
        &mut self,
        module: &ModuleWithInfo,
        (func_handle, fun): (crate::Handle<crate::Function>, &crate::Function),
    ) -> Result<FunctionSummary, BoundsCheckError> {
        // Get the function info from the module
        let func_info = &module.info[func_handle];
        // Exit early if the function can kill, as this isn't supported.
        if func_info.may_kill {
            return Err(BoundsCheckError::Unsupported(
                "Functions that can kill invocations.".to_string(),
            ));
        }
        // Make the function name
        let func_name = self.func_to_name(&module.module, func_handle);
        // Calculate the number of arguments, returning an error if there are too many.
        let nargs: u8 = fun.arguments.len().try_into().map_err(|e| {
            BoundsCheckError::Unsupported("Too many function arguments".to_string())
        })?;

        let ret_ty = match fun.result {
            Some(crate::FunctionResult { ty, .. }) => self[ty].clone(),
            None => self.helper.none_type(),
        };

        // Create the bounds info struct that we use to populate the constraints on the function.
        let mut func_bounds_info = PartialFunctionSummary {
            expressions: Default::default(),
            arguments: Vec::with_capacity(fun.arguments.len()),
            local_variabes: Vec::with_capacity(fun.local_variables.len()),
            ret_ty,
        };

        for (var_handle, var) in fun.local_variables.iter() {
            let var = self.mark_var(var_handle, var, &func_name)?;
            func_bounds_info.local_variabes.push(var);
        }

        // begin the summary.
        self.helper.begin_summary(func_name, nargs)?;

        if let Some(crate::FunctionResult { ty, .. }) = fun.result {
            let ty = self[ty].clone();
            self.helper.mark_return_type(ty)?;
        }

        for (pos, arg) in fun.arguments.iter().enumerate() {
            let name = arg
                .to_name()
                .clone()
                .unwrap_or(String::from("$anon_arg_") + &pos.to_string());
            // Get the variable handle..
            let var = self
                .helper
                .declare_var(abc_helper::Var { name: name.into() })?;

            func_bounds_info.arguments.push(var.clone());

            // Mark the type of the function argument..
            let ty = self.types[arg.to_type().index()].clone();
            self.helper.mark_type(var.clone(), ty.clone())?;
        }

        // Now, go through the body of the function
        let func_with_info = FunctionWithInfo {
            handle: func_handle,
            func: fun,
            info: func_info,
        };

        self.visit_block(
            &fun.body,
            module,
            &func_with_info,
            &mut func_bounds_info,
            None,
        )?;

        // End the summary
        let summary = self.helper.end_summary()?;

        Ok(func_bounds_info.to_function_summary(summary))
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
        lhs: ConstraintHandle<AbcExpression>,
        rhs: ConstraintHandle<AbcExpression>,
    ) -> Result<ConstraintHandle<AbcExpression>, BoundsCheckError> {
        use crate::BinaryOperator;
        use abc_helper::BinaryOp;
        use abc_helper::CmpOp;
        use abc_helper::Predicate;
        if let Some(binop) = op.try_into().ok() {
            Ok(AbcExpression::new_binary_op(binop, lhs, rhs).into())
        } else if let Some(cmpop) = op.try_into().ok() {
            let pred = Predicate::new_comparison(cmpop, lhs, rhs);
            Ok(AbcExpression::new_pred(pred).into())
        } else {
            match op {
                BinaryOperator::LogicalAnd => {
                    let pred = Predicate::new_and(
                        Predicate::from_expression_handle(lhs),
                        Predicate::from_expression_handle(rhs),
                    );
                    Ok(AbcExpression::new_pred(pred).into())
                }
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
    ) -> Result<ConstraintHandle<AbcExpression>, BoundsCheckError> {
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
        let res: ConstraintHandle<AbcExpression> = match expr {
            Expr::Literal(t) => ABCExpr::Literal(format!("{t}")),
            Expr::Constant(c) => ABCExpr::Var(self[*c].clone()),
            Expr::Binary { op, left, right } => {
                let left = self.global_expression_resolution(*left, module)?;
                let right = self.global_expression_resolution(*right, module)?;
                // A binary op with a boolean result maps to a predicate
                // Otherwise, it maps to a binary op.
                let bin_op: Option<abc_helper::BinaryOp> = (*op).try_into().ok();
                match bin_op {
                    Some(t) => ABCExpr::BinaryOp(t, left, right),
                    None => {
                        // Convert the op into a predicate...
                        let op = (*op).try_into().map_err(|_| {
                            BoundsCheckError::Unsupported(format!(
                                "Unsupported binary op: {:?}",
                                op
                            ))
                        })?;
                        ABCExpr::Pred(
                            abc_helper::Predicate::new_comparison(op, left.clone(), right.clone())
                                .into(),
                        )
                    }
                }
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
            let cnst_as_expr: AbcExpression = cnst.into();

            // Resolve the initialization to an expression handle
            let expr =
                self.global_expression_resolution(var.init, &ModuleWithInfo { module, info })?;

            // Mark the constraint of the initialization.
            self.helper.add_constraint(
                cnst_as_expr.into(),
                abc_helper::ConstraintOp::Assign,
                expr,
            )?;
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

        for fun in module.functions.iter() {
            let new_summary = self.check_function(&ModuleWithInfo { module, info }, fun)?;
            self.functions.push(new_summary);
        }

        // Entry points contain function summaries.
        // for ep in module.entry_points.iter() {
        //     let new_summary = self.check_function(&ModuleWithInfo { module, info }, ep.function)?;
        //     // I must be able to mark additional constraints within the function.
        //     // E.g., the arguments to the function must correspond to
        //     self.entry_points.push(new_summary);
        // }

        Ok(())
    }
}
