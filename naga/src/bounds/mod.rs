mod analyzer;
mod helper_interface;

mod utils;
mod visitor;

pub use analyzer::BoundsCheckResult;
pub use analyzer::BoundsChecker;

bitflags::bitflags! {
    /// Flags that specify which address spaces must have their bounds checked for index accesses.
    /// By default, this is set to `all`.
    ///
    /// This is different from [`BoundsCheckPolicy`], which dictates how out of bounds accesses should be handled.
    /// Instead, this flag specifies which address spaces should have explicit bounds checks inserted.
    ///
    /// Useful for backends that have automatic robustness checks for certain spaces, such as Vulkan and D3D
    ///
    /// [`BoundsCheckPolicy`]: crate::proc::BoundsCheckPolicy
    #[derive(Clone, Copy)]
    pub struct AddressSpacesToCheck: u8 {
        const Function = 1;
        const Private = 1 << 1;
        const WorkGroup = 1 << 2;
        const Uniform = 1 << 3;
        const Storage = 1 << 4;
    }
}

impl Default for AddressSpacesToCheck {
    fn default() -> Self {
        AddressSpacesToCheck::all()
    }
}

impl AddressSpacesToCheck {
    /// Given an address space, return whether the corresponding flag is set in `self`.
    pub const fn contains_address_space(&self, space: crate::AddressSpace) -> bool {
        match space {
            crate::AddressSpace::Function => self.contains(AddressSpacesToCheck::Function),
            crate::AddressSpace::Private => self.contains(AddressSpacesToCheck::Private),
            crate::AddressSpace::WorkGroup => self.contains(AddressSpacesToCheck::WorkGroup),
            crate::AddressSpace::Uniform => self.contains(AddressSpacesToCheck::Uniform),
            crate::AddressSpace::Storage { .. } => self.contains(AddressSpacesToCheck::Storage),
            _ => false,
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
    BadHandle(#[from] crate::arena::BadHandle),
    #[error("{0}")]
    ConstraintHelperError(#[from] abc_helper::ConstraintError),
    #[error("{0}")]
    SolverError(#[from] abc_helper::SolverError),
    #[error("Store to non pointer expression")]
    StoreToNonPointer,
    #[error("Unsupported loop structure detected")]
    UnsupportedLoopStructure,
    #[error("Expecting a vector")]
    ExpectingVector,

    #[error("VisitorError({0})")]
    VisitorError(#[from] visitor::VisitorError),
}


/// Constructs a JSON report for the provided bounds check results and the source code.
pub fn report_to_json(constraints: &[BoundsCheckResult], source: &str) -> String {
    let mut output = String::new();
    output.extend(&['{', '\n']);
    let mut constraints = constraints.iter().peekable();
    while let Some(constraint) = constraints.next() {
        // Print the expression that caused the constraint.
        let Some(span) = constraint.get_span().to_range() else {
            continue;
        };
        let content = &source[span];
        let result = constraint.get_result();
        output.push_str("\t{{\n\t\tline: ");
        output.push_str(content);
        output.push_str(",\n\t\result: [\n");
        let Some((last, results)) = result.split_last() else {
            continue;
        };
        for interval in results {
            output.push_str("\t\t\t\t");
            output.push_str(interval.pretty_print().to_string().as_str());
            output.push_str(",\n");
        }
        output.push_str("\t\t\t\t");
        output.push_str(last.pretty_print().to_string().as_str());
        output.push_str("\n\t\t\t]\n\t}}");
        // json requires no trailing comma...
        if constraints.peek().is_some() {
            output.push_str(",\n");
        } else {
            output.push('\n');
        }
    }
    output.extend(&['}', '\n']);
    output
}