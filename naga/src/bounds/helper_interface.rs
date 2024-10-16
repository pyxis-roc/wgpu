use abc_helper::{AbcScalar, BinaryOp, CmpOp};

impl From<crate::VectorSize> for std::num::NonZeroU8 {
    fn from(size: crate::VectorSize) -> Self {
        match size {
            crate::VectorSize::Quad => unsafe { std::num::NonZeroU8::new_unchecked(4) },
            crate::VectorSize::Tri => unsafe { std::num::NonZeroU8::new_unchecked(3) },
            crate::VectorSize::Bi => unsafe { std::num::NonZeroU8::new_unchecked(2) },
        }
    }
}

impl From<crate::VectorSize> for std::num::NonZeroU32 {
    fn from(size: crate::VectorSize) -> Self {
        match size {
            crate::VectorSize::Quad => unsafe { std::num::NonZeroU32::new_unchecked(4) },
            crate::VectorSize::Tri => unsafe { std::num::NonZeroU32::new_unchecked(3) },
            crate::VectorSize::Bi => unsafe { std::num::NonZeroU32::new_unchecked(2) },
        }
    }
}

impl std::fmt::Display for crate::Literal {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        use crate::Literal;
        match *self {
            Literal::F64(flt) | Literal::AbstractFloat(flt) => write!(f, "{}", flt),
            Literal::F32(flt) => write!(f, "{}", flt),
            Literal::Bool(b) => write!(f, "{}", b),
            Literal::I64(i) | Literal::AbstractInt(i) => write!(f, "{}", i),
            Literal::U64(u) => write!(f, "{}", u),
            Literal::I32(i) => write!(f, "{}", i),
            Literal::U32(u) => write!(f, "{}", u),
        }
    }
}

impl TryFrom<crate::BinaryOperator> for BinaryOp {
    type Error = &'static str;

    fn try_from(op: crate::BinaryOperator) -> Result<Self, Self::Error> {
        use crate::BinaryOperator as B;
        use BinaryOp as A;
        Ok(match op {
            B::Add => A::Plus,
            B::Subtract => A::Minus,
            B::Multiply => A::Times,
            B::Divide => A::Div,
            B::Modulo => A::Mod,
            B::ExclusiveOr => A::BitXor,
            B::InclusiveOr => A::BitOr,
            B::And => A::BitAnd,
            B::ShiftLeft => A::Shl,
            B::ShiftRight => A::Shr,
            _ => return Err("Not a binary operator."),
        })
    }
}

impl TryFrom<crate::BinaryOperator> for CmpOp {
    type Error = &'static str;

    fn try_from(op: crate::BinaryOperator) -> Result<Self, Self::Error> {
        use crate::BinaryOperator as B;
        use CmpOp as A;
        Ok(match op {
            B::Equal => A::Eq,
            B::NotEqual => A::Neq,
            B::Less => A::Lt,
            B::LessEqual => A::Leq,
            B::Greater => A::Gt,
            B::GreaterEqual => A::Geq,
            _ => return Err("Not a comparison operator."),
        })
    }
}

impl From<crate::Scalar> for AbcScalar {
    fn from(scalar: crate::Scalar) -> Self {
        use crate::ScalarKind;
        match scalar.kind {
            ScalarKind::Sint => AbcScalar::Sint(scalar.width),
            ScalarKind::Uint => AbcScalar::Uint(scalar.width),
            ScalarKind::Float => AbcScalar::Float(scalar.width),
            ScalarKind::Bool => AbcScalar::Bool,
            ScalarKind::AbstractFloat => AbcScalar::AbstractFloat,
            ScalarKind::AbstractInt => AbcScalar::AbstractInt,
        }
    }
}

// impl From<crate::ScalarKind> for AbcScalar {

// }

pub(crate) trait HasName {
    fn to_name(&self) -> &Option<String>;
}

impl HasName for crate::Override {
    fn to_name(&self) -> &Option<String> {
        &self.name
    }
}

impl HasName for crate::Constant {
    fn to_name(&self) -> &Option<String> {
        &self.name
    }
}

impl HasName for crate::Type {
    fn to_name(&self) -> &Option<String> {
        &self.name
    }
}

impl HasName for crate::FunctionArgument {
    fn to_name(&self) -> &Option<String> {
        &self.name
    }
}

impl HasName for crate::GlobalVariable {
    fn to_name(&self) -> &Option<String> {
        &self.name
    }
}

impl HasType for crate::GlobalVariable {
    fn to_type(&self) -> crate::Handle<crate::Type> {
        self.ty
    }
}

impl HasName for crate::LocalVariable {
    fn to_name(&self) -> &Option<String> {
        &self.name
    }
}

pub(crate) trait HasType {
    fn to_type(&self) -> crate::Handle<crate::Type>;
}

impl HasType for crate::Constant {
    fn to_type(&self) -> crate::Handle<crate::Type> {
        self.ty
    }
}

impl HasType for crate::Override {
    fn to_type(&self) -> crate::Handle<crate::Type> {
        self.ty
    }
}

impl HasType for crate::FunctionArgument {
    fn to_type(&self) -> crate::Handle<crate::Type> {
        self.ty
    }
}

impl HasType for crate::LocalVariable {
    fn to_type(&self) -> crate::Handle<crate::Type> {
        self.ty
    }
}

impl From<crate::Literal> for abc_helper::Term {
    fn from(value: crate::Literal) -> Self {
        match value {
            crate::Literal::F64(flt) => {
                abc_helper::Term::Literal(abc_helper::Literal::AbstractFloat(flt))
            }
            crate::Literal::AbstractFloat(flt) => {
                abc_helper::Term::Literal(abc_helper::Literal::AbstractFloat(flt))
            }
            crate::Literal::F32(flt) => Self::Literal(flt.into()),
            crate::Literal::Bool(true) => Self::new_literal_true(),
            crate::Literal::Bool(false) => Self::new_literal_false(),
            crate::Literal::I64(i) => Self::Literal(i.into()),
            crate::Literal::U64(u) => Self::Literal(u.into()),
            crate::Literal::I32(i) => Self::Literal(i.into()),
            crate::Literal::U32(u) => Self::Literal(u.into()),
            crate::Literal::AbstractInt(i) => Self::Literal(abc_helper::Literal::AbstractInt(i)),
        }
    }
}
