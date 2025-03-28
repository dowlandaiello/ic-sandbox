use crate::parser::Expr;
use ast_ext::Spanned;
use std::{collections::BTreeSet, fmt};

#[derive(Clone, Debug, PartialEq)]
pub enum UntypedExpr {
    Id(String),
    Abstraction {
        bind_id: String,
        body: Box<UntypedExpr>,
    },
    Application {
        lhs: Box<UntypedExpr>,
        rhs: Box<UntypedExpr>,
    },
}

impl UntypedExpr {
    pub fn free_vars<'a>(&'a self) -> BTreeSet<&'a str> {
        match &self {
            Self::Id(i) => BTreeSet::from_iter([i.as_str()]),
            Self::Abstraction { bind_id, body, .. } => {
                let mut all = body.free_vars();
                all.remove(bind_id.as_str());

                all
            }
            Self::Application { lhs, rhs } => {
                let mut lhs_free = lhs.free_vars();
                lhs_free.extend(&rhs.free_vars());

                lhs_free
            }
        }
    }

    pub fn contains_var(&self, v: &str) -> bool {
        self.free_vars().iter().any(|x| x == &v)
    }

    pub fn contains_lambda(&self) -> bool {
        match self {
            Self::Id(_) => false,
            Self::Abstraction { .. } => true,
            Self::Application { lhs, rhs } => lhs.contains_lambda() || rhs.contains_lambda(),
        }
    }

    pub fn as_id(&self) -> Option<&str> {
        match self {
            Self::Id(s) => Some(s),
            _ => None,
        }
    }
}

impl fmt::Display for UntypedExpr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Id(s) => write!(f, "{}", s),
            Self::Abstraction { bind_id, body } => write!(f, "\\{}.{}", bind_id, body),
            Self::Application { lhs, rhs } => {
                write!(f, "({} {})", lhs, rhs)
            }
        }
    }
}

pub fn typecheck(_e: Spanned<Expr>) -> UntypedExpr {}
