use std::fmt::{self, Display, Formatter};

use crate::{BddId, BddManager};

/// A boolean expression tree.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Exp {
    Var(String),
    Not(Box<Exp>),
    And(Box<Exp>, Box<Exp>),
    Or(Box<Exp>, Box<Exp>),
    Xor(Box<Exp>, Box<Exp>),
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

    #[inline]
    pub fn xor(e1: Box<Exp>, e2: Box<Exp>) -> Box<Self> {
        Box::new(Exp::Xor(e1, e2))
    }
}

impl BddManager {
    /// Gets or inserts the BDD for an expression.
    pub fn insert_exp(&self, e: &Exp) -> BddId {
        match e {
            Exp::Var(var) => self.insert_var(var),
            Exp::Not(e) => {
                let bdd_e = self.insert_exp(e);
                self.insert_not(bdd_e)
            }
            Exp::And(e1, e2) => {
                let bdd_e1 = self.insert_exp(e1);
                let bdd_e2 = self.insert_exp(e2);
                self.insert_and(bdd_e1, bdd_e2)
            }
            Exp::Or(e1, e2) => {
                let bdd_e1 = self.insert_exp(e1);
                let bdd_e2 = self.insert_exp(e2);
                self.insert_or(bdd_e1, bdd_e2)
            }
            Exp::Xor(e1, e2) => {
                let bdd_e1 = self.insert_exp(e1);
                let bdd_e2 = self.insert_exp(e2);
                self.insert_xor(bdd_e1, bdd_e2)
            }
        }
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
                paren!(e, Exp::And(_, _) | Exp::Or(_, _) | Exp::Xor(_, _))
            }
            Exp::And(e1, e2) => {
                paren!(e1, Exp::Or(_, _) | Exp::Xor(_, _))?;
                write!(f, " ∧ ")?;
                paren!(e2, Exp::And(_, _) | Exp::Or(_, _) | Exp::Xor(_, _))
            }
            Exp::Or(e1, e2) => {
                paren!(e1, Exp::And(_, _) | Exp::Xor(_, _))?;
                write!(f, " ∨ ")?;
                paren!(e2, Exp::And(_, _) | Exp::Or(_, _) | Exp::Xor(_, _))
            }
            Exp::Xor(e1, e2) => {
                paren!(e1, Exp::And(_, _) | Exp::Or(_, _))?;
                write!(f, " ⊕ ")?;
                paren!(e2, Exp::And(_, _) | Exp::Or(_, _) | Exp::Xor(_, _))
            }
        }
    }
}
