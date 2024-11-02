#![allow(unused_macros)]
/// Macro used only for debugging purposes that resolves to the name of the expression.
/// # Example
/// ```rust,ignore
/// let expr = Expression::Constant { value: 0 };
/// assert_eq!(expression_variant!(expr), "Constant");
/// ```
#[allow(unused_macros)]
#[macro_export]
macro_rules! expression_variant {
    ($expr:expr) => {
        match $expr {
            $crate::Expression::Literal { .. } => "Literal",
            $crate::Expression::Constant { .. } => "Constant",
            $crate::Expression::Override { .. } => "Override",
            $crate::Expression::ZeroValue { .. } => "ZeroValue",
            $crate::Expression::Compose { .. } => "Compose",
            $crate::Expression::Access { .. } => "Access",
            $crate::Expression::AccessIndex { .. } => "AccessIndex",
            $crate::Expression::Splat { .. } => "Splat",
            $crate::Expression::Swizzle { .. } => "Swizzle",
            $crate::Expression::FunctionArgument(..) => "FunctionArgument",
            $crate::Expression::GlobalVariable(..) => "GlobalVariable",
            $crate::Expression::LocalVariable(..) => "LocalVariable",
            $crate::Expression::Load { .. } => "Load",
            $crate::Expression::ImageSample { .. } => "ImageSample",
            $crate::Expression::ImageLoad { .. } => "ImageLoad",
            $crate::Expression::ImageQuery { .. } => "ImageQuery",
            $crate::Expression::Unary { .. } => "Unary",
            $crate::Expression::Binary { .. } => "Binary",
            $crate::Expression::Select { .. } => "Select",
            $crate::Expression::Derivative { .. } => "Derivative",
            $crate::Expression::Relational { .. } => "Relational",
            $crate::Expression::Math { .. } => "Math",
            $crate::Expression::As { .. } => "As",
            $crate::Expression::CallResult { .. } => "CallResult",
            $crate::Expression::AtomicResult { .. } => "AtomicResult",
            $crate::Expression::WorkGroupUniformLoadResult { .. } => "WorkGroupUniformLoadResult",
            $crate::Expression::ArrayLength(..) => "ArrayLength",
            $crate::Expression::RayQueryProceedResult { .. } => "RayQueryProceedResult",
            $crate::Expression::RayQueryGetIntersection { .. } => "RayQueryGetIntersection",
            $crate::Expression::SubgroupBallotResult { .. } => "SubgroupBallotResult",
            $crate::Expression::SubgroupOperationResult { .. } => "SubgroupOperationResult",
            // In case new expressions are added in the future...
            #[allow(unreachable_patterns)]
            _ => "UNKNOWN_EXPR_KIND",
        }
    };
}

/// Macro used only for debugging purposes that prints the variant of a statement.
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

#[allow(unused_imports)]
pub(super) use {expression_variant, statement_variant};
