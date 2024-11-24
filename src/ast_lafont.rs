use super::UNIT_STR;
use std::fmt;

#[derive(Eq, Clone, Debug, PartialEq)]
pub struct Ident(pub String);

impl fmt::Display for Ident {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

#[derive(Eq, Clone, Debug, PartialEq)]
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
    Semicolon,
    Colon,
    Comma,
    PlusOutput,
    MinusInput,
    Unit,
    NonDiscPartStart,
    NonDiscPartEnd,
    LeftSquareBracket,
    RightSquareBracket,
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
            Self::Semicolon => write!(f, ";"),
            Self::Colon => write!(f, ":"),
            Self::Comma => write!(f, ","),
            Self::PlusOutput => write!(f, "+"),
            Self::MinusInput => write!(f, "-"),
            Self::Unit => write!(f, "()"),
            Self::NonDiscPartStart => write!(f, "{{"),
            Self::NonDiscPartEnd => write!(f, "}}"),
            Self::LeftSquareBracket => write!(f, "["),
            Self::RightSquareBracket => write!(f, "]"),
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

#[derive(Eq, Clone, Debug, PartialEq)]
pub enum Expr {
    TypeDec(Type),
    Symbol { ident: Ident, ports: Vec<PortKind> },
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

#[derive(Eq, Clone, Debug, PartialEq)]
pub struct Net {
    pub lhs: Option<Agent>,
    pub rhs: Option<Agent>,
}

#[derive(Eq, Clone, Debug, PartialEq)]
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

#[derive(Eq, Clone, Debug, PartialEq)]
pub enum PortKind {
    Input(Type),
    Output(Type),
    Partition(Vec<Port>),
}

impl fmt::Display for PortKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Input(ty) => write!(f, "{}-", ty.0),
            Self::Output(ty) => write!(f, "{}+", ty.0),
            Self::Partition(p) => write!(
                f,
                "[{}]",
                p.iter()
                    .map(|p| p.to_string())
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
        }
    }
}

#[derive(Eq, Clone, Debug, PartialEq)]
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
