use super::UNIT_STR;
use std::fmt;

#[derive(Ord, PartialOrd, Hash, Eq, Clone, Debug, PartialEq)]
pub struct Ident(pub String);

impl fmt::Display for Ident {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

#[derive(Ord, PartialOrd, Hash, Eq, Clone, Debug, PartialEq)]
pub struct Type(pub String);

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

#[derive(Eq, Hash, Clone, Debug, PartialEq)]
pub enum Token {
    Keyword(Keyword),
    Ident(String),
    Colon,
    Comma,
    PlusOutput,
    MinusInput,
    Unit,
    NonDiscPartStart,
    NonDiscPartEnd,
    LeftParen,
    RightParen,
    ActivePair,
}

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Keyword(Keyword::Type) => write!(f, "type"),
            Self::Keyword(Keyword::Symbol) => write!(f, "symbol"),
            Self::Ident(s) => write!(f, "{}", s),
            Self::Colon => write!(f, ":"),
            Self::Comma => write!(f, ","),
            Self::PlusOutput => write!(f, "+"),
            Self::MinusInput => write!(f, "-"),
            Self::Unit => write!(f, "()"),
            Self::NonDiscPartStart => write!(f, "{{"),
            Self::NonDiscPartEnd => write!(f, "}}"),
            Self::LeftParen => write!(f, "("),
            Self::RightParen => write!(f, ")"),
            Self::ActivePair => write!(f, "><"),
        }
    }
}

#[derive(Eq, PartialEq, Hash, Clone, Debug)]
pub enum Keyword {
    Type,
    Symbol,
}

impl fmt::Display for Keyword {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Type => write!(f, "type"),
            Self::Symbol => write!(f, "symbol"),
        }
    }
}

#[derive(Hash, Eq, Clone, Debug, PartialEq)]
pub enum Expr {
    TypeDec(Type),
    Symbol {
        ident: Ident,
        ports: Vec<PortGrouping>,
    },
    Net(Net),
}

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::TypeDec(ty) => write!(f, "type {}", ty.0),
            Self::Symbol { ident, ports } => write!(
                f,
                "symbol {}: {}",
                ident.0,
                ports
                    .iter()
                    .map(|p| p.to_string())
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
            Self::Net(Net { lhs, rhs }) => {
                write!(
                    f,
                    "{} >< {}",
                    lhs.as_ref()
                        .map(|s| s.to_string())
                        .unwrap_or(UNIT_STR.to_owned()),
                    rhs.as_ref()
                        .map(|s| s.to_string())
                        .unwrap_or(UNIT_STR.to_owned())
                )
            }
        }
    }
}

#[derive(Hash, Eq, Clone, Debug, PartialEq)]
pub struct Net {
    pub lhs: Option<Agent>,
    pub rhs: Option<Agent>,
}

#[derive(Hash, Eq, Clone, Debug, PartialEq)]
pub struct Agent {
    pub name: Ident,
    pub ports: Vec<Port>,
}

impl fmt::Display for Agent {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}({})",
            self.name.0,
            self.ports
                .iter()
                .map(|p| p.to_string())
                .collect::<Vec<_>>()
                .join(", ")
        )
    }
}

#[derive(Hash, Eq, Clone, Debug, PartialEq)]
pub enum PortGrouping {
    Singleton(PortKind),
    Partition(Vec<PortKind>),
}

impl fmt::Display for PortGrouping {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Singleton(p) => {
                write!(f, "{}", p)
            }
            Self::Partition(ps) => {
                write!(
                    f,
                    "[{}]",
                    ps.iter()
                        .map(|p| p.to_string())
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            }
        }
    }
}

#[derive(Hash, Eq, Clone, Debug, PartialEq)]
pub enum PortKind {
    Input(Type),
    Output(Type),
}

impl fmt::Display for PortKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Input(ty) => write!(f, "{}-", ty.0),
            Self::Output(ty) => write!(f, "{}+", ty.0),
        }
    }
}

#[derive(Hash, Eq, Clone, Debug, PartialEq)]
pub enum Port {
    Agent(Agent),
    Var(Ident),
}

impl fmt::Display for Port {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Agent(a) => write!(f, "{}", a),
            Self::Var(v) => write!(f, "{}", v.0),
        }
    }
}
