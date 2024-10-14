mod analyzer;
mod helper_interface;

pub use analyzer::BoundsChecker;

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
    BadHandle(#[from] crate::arena::BadHandle),
    #[error("{0}")]
    ConstraintHelperError(#[from] abc_helper::ConstraintError),
    #[error("Store to non pointer expression")]
    StoreToNonPointer,
    #[error("Unsupported loop structure detected")]
    UnsupportedLoopStructure,
}
