use std::fmt::{self, Display, Formatter};

/// A boolean expression tree.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Exp {
    Var(String),
    Not(Box<Exp>),
    And(Box<Exp>, Box<Exp>),
    Or(Box<Exp>, Box<Exp>),
}

impl Exp {
    #[inline]
    pub fn var<S: Into<String>>(ident: S) -> Box<Self> {
        Box::new(Exp::Var(ident.into()))
    }

    #[inline]
    pub fn not(e: Box<Exp>) -> Box<Self> {
        Box::new(Exp::Not(e))
    }

    #[inline]
    pub fn and(e1: Box<Exp>, e2: Box<Exp>) -> Box<Self> {
        Box::new(Exp::And(e1, e2))
    }

    #[inline]
    pub fn or(e1: Box<Exp>, e2: Box<Exp>) -> Box<Self> {
        Box::new(Exp::Or(e1, e2))
    }
}

impl Display for Exp {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        macro_rules! paren(($e:expr, $needs_paren:pat) => {
            match $e.as_ref() {
                $needs_paren => write!(f, "({})", $e),
                _ => write!(f, "{}", $e),
            }
        });
        match self {
            Exp::Var(var) => write!(f, "{var}"),
            Exp::Not(e) => {
                write!(f, "¬")?;
                paren!(e, Exp::And(_, _) | Exp::Or(_, _))
            }
            Exp::And(e1, e2) => {
                paren!(e1, Exp::Or(_, _))?;
                write!(f, " ∧ ")?;
                paren!(e2, Exp::And(_, _) | Exp::Or(_, _))
            }
            Exp::Or(e1, e2) => {
                paren!(e1, Exp::And(_, _))?;
                write!(f, " ∨ ")?;
                paren!(e2, Exp::And(_, _) | Exp::Or(_, _))
            }
        }
    }
}
