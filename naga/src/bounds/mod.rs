mod analyzer;
mod helper_interface;

pub use analyzer::BoundsChecker;
// /// The information returned by the bounds checker analysis..
// #[derive(Clone, Debug)]
// #[cfg_attr(feature = "serialize", derive(serde::Serialize))]
// #[cfg_attr(feature = "deserialize", derive(serde::Deserialize))]
// pub struct ExpressionBoundInfo {
//     pub constraints: Vec<
// }

// pub struct FunctionBoundInfo {
//     expressions: Box<[ExpressionBoundInfo]>,
// }
// pub struct BoundsInfo {
//     /// Vector of bounds information for functions. Index is the index of the handle
//     functions: Vec<FunctionBoundInfo>,
//     /// Vector of bounds inf
//     entry_points: Vec<FunctionBoundInfo>,
// }

//TODO: analyze the model at the same time as we validate it,
// merge the corresponding matches over expressions and statements.

// To start with, this analyzer is just going to print out the access requirements for each expression...

// pub use analyzer::{ExpressionInfo, FunctionBounds, Uniformity, UniformityRequirements};

// #[derive(Debug, Clone)]
// #[cfg_attr(feature = "serialize", derive(serde::Serialize))]
// #[cfg_attr(feature = "deserialize", derive(serde::Deserialize))]
// pub struct BoundsInfo {
//     functions: Vec<FunctionBounds>,
//     entry_points: Vec<FunctionBounds>,
//     // For sanity checking, anything we eliminate here is based on an assumption about some expression involving constants.
//     // This can be evaluated as const...
//     // Assumptions that are able to be checked at translation time...
//     assumptions: FastHashSet<Handle<crate::Expression>>,
// }

// impl ops::Index<Handle<crate::Type>> for ModuleInfo {
//     type Output = TypeFlags;
//     fn index(&self, handle: Handle<crate::Type>) -> &Self::Output {
//         &self.type_flags[handle.index()]
//     }
// }

// impl ops::Index<Handle<crate::Function>> for ModuleInfo {
//     type Output = FunctionInfo;
//     fn index(&self, handle: Handle<crate::Function>) -> &Self::Output {
//         &self.functions[handle.index()]
//     }
// }

// impl ops::Index<Handle<crate::Expression>> for ModuleInfo {
//     type Output = TypeResolution;
//     fn index(&self, handle: Handle<crate::Expression>) -> &Self::Output {
//         &self.const_expression_types[handle.index()]
//     }
// }
