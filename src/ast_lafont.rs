use std::fmt;

#[derive(Debug, PartialEq)]
pub struct Ident(pub String);

#[derive(Debug, PartialEq)]
pub struct Type(pub String);

#[derive(Debug, PartialEq)]
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

#[derive(Debug, PartialEq)]
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

#[derive(Debug, PartialEq)]
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
                write!(f, "{} >< {}", lhs, rhs)
            }
        }
    }
}

#[derive(Debug, PartialEq)]
pub struct Net {
    pub lhs: Agent,
    pub rhs: Agent,
}

#[derive(Debug, PartialEq)]
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

#[derive(Debug, PartialEq)]
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

#[derive(Debug, PartialEq)]
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
