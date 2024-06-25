use std::{
    cmp::Ordering,
    fmt::{self, Display, Formatter},
};

/// A boolean variable.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Var(usize);

/// A boolean expression tree.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Exp {
    Var(Var),
    Not(Box<Exp>),
    And(Box<Exp>, Box<Exp>),
    Or(Box<Exp>, Box<Exp>),
}

impl Var {
    pub const ZERO: Var = Var(0);
    pub const ONE: Var = Var(1);

    #[inline]
    pub fn new(var: usize) -> Self {
        Var(var.checked_add(2).unwrap())
    }
}

impl Exp {
    #[inline]
    pub fn var(var: usize) -> Box<Self> {
        Box::new(Exp::Var(Var::new(var)))
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

impl PartialOrd for Var {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Var {
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        // Order variables first, then 0, then 1.
        self.0.wrapping_sub(2).cmp(&other.0.wrapping_sub(2))
    }
}

impl Display for Var {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        if self.0 <= 1 {
            return write!(f, "{}", self.0);
        }
        let var = self.0 - 2;
        let name = unsafe { char::from_u32_unchecked((var % 26) as u32 + 'a' as u32) };
        let number = var / 26;
        write!(f, "{name}")?;
        if number != 0 {
            write!(f, "{number}")?;
        }
        Ok(())
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
