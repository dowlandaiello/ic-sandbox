use crate::UNIT_STR;
use serde::{Deserialize, Serialize};
use std::{
    collections::{BTreeSet, VecDeque},
    fmt, ptr,
};

#[derive(Serialize, Deserialize, Ord, PartialOrd, Hash, Eq, Clone, Debug, PartialEq)]
pub struct Ident(pub String);

impl fmt::Display for Ident {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

#[derive(Serialize, Deserialize, Ord, PartialOrd, Hash, Eq, Clone, Debug, PartialEq)]
pub struct Type(pub String);

impl Into<Type> for String {
    fn into(self) -> Type {
        Type(self)
    }
}

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
        ident: Type,
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

#[derive(Ord, PartialOrd, Hash, Eq, Clone, Debug, PartialEq)]
pub struct Net {
    pub lhs: Option<Agent>,
    pub rhs: Option<Agent>,
}

impl Net {
    pub fn replace_name(&mut self, name: Ident, val: Port) {
        if let Some(lhs) = self.lhs.take() {
            self.lhs = Some(lhs.replace_name(&name, &val));
        }

        if let Some(rhs) = self.rhs.take() {
            self.rhs = Some(rhs.replace_name(&name, &val));
        }
    }

    /// Gets a list of all the names mentioned in the net.
    pub fn names_mentioned(&self) -> Vec<Type> {
        let mut to_check = VecDeque::from_iter(
            [&self.lhs, &self.rhs]
                .into_iter()
                .filter_map(|x| x.as_ref()),
        );
        let mut names = Vec::default();

        while let Some(c) = to_check.pop_front() {
            names.push(c.name.clone());

            for p in c.ports.iter() {
                match p {
                    Port::Var(v) => {
                        names.push(Type(v.0.clone()));
                    }
                    Port::Agent(a) => {
                        to_check.push_back(&a);
                    }
                }
            }
        }

        names
    }
}

impl fmt::Display for Net {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match (self.lhs.as_ref(), self.rhs.as_ref()) {
            (Some(lhs), Some(rhs)) => {
                write!(f, "{} >< {}", lhs, rhs)
            }
            (Some(lhs), None) | (None, Some(lhs)) => {
                write!(f, "{}", lhs)
            }
            (None, None) => write!(f, ""),
        }
    }
}

#[derive(Serialize, Deserialize, Ord, PartialOrd, Hash, Eq, Clone, Debug, PartialEq)]
pub struct Agent {
    pub name: Type,
    pub ports: Vec<Port>,
}

impl Agent {
    pub fn new(name: impl Into<Type>) -> Self {
        Self {
            name: name.into(),
            ports: Default::default(),
        }
    }

    pub fn iter_child_agents<'a>(&'a self) -> impl Iterator<Item = PortView> + 'a {
        PortWalker::new(self)
    }

    pub fn replace_name(mut self, name: &Ident, val: &Port) -> Self {
        self.ports = self
            .ports
            .drain(..)
            .map(|p| match p {
                Port::Agent(a) => Port::Agent(a.replace_name(name, val)),
                Port::Var(v) => {
                    if v.0 == name.0 {
                        val.clone()
                    } else {
                        Port::Var(v.clone())
                    }
                }
            })
            .collect();

        self
    }

    // TODO: Make this iterative, as well
    pub fn vars_mentioned(&self) -> Vec<Ident> {
        self.ports
            .iter()
            .map(|p| match p {
                Port::Var(v) => vec![v.clone()],
                Port::Agent(a) => a.vars_mentioned(),
            })
            .flatten()
            .collect()
    }

    pub fn pair_ord<'a>(a: Option<Self>, b: Option<Self>) -> (Option<Self>, Option<Self>) {
        if a < b {
            (a, b)
        } else {
            (b, a)
        }
    }
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

#[derive(Ord, PartialOrd, Hash, Eq, Clone, Debug, PartialEq)]
pub enum PortView<'a> {
    Agent(&'a Agent),
    Var(&'a Ident),
}

pub struct PortWalker<'a> {
    to_visit: VecDeque<PortView<'a>>,
    seen: BTreeSet<*const Agent>,
}

impl<'a> PortWalker<'a> {
    pub fn new(start: &'a Agent) -> Self {
        Self {
            to_visit: VecDeque::from_iter([PortView::Agent(start)]),
            seen: Default::default(),
        }
    }
}

impl<'a> Iterator for PortWalker<'a> {
    type Item = PortView<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        let mut to_visit = self
            .to_visit
            .drain(..)
            .skip_while(|x| {
                if let PortView::Agent(a) = x {
                    self.seen.contains(&ptr::addr_of!(**a))
                } else {
                    false
                }
            })
            .collect::<VecDeque<_>>();
        let curr_ptr = to_visit.pop_front()?;

        self.to_visit = to_visit;

        if let PortView::Agent(a) = curr_ptr {
            self.seen.insert(ptr::addr_of!(*a));

            self.to_visit.extend(a.ports.iter().map(|p| match p {
                Port::Agent(a) => PortView::Agent(a),
                Port::Var(v) => PortView::Var(v),
            }));
        }

        Some(curr_ptr)
    }
}

#[derive(Serialize, Deserialize, Ord, PartialOrd, Hash, Eq, Clone, Debug, PartialEq)]
pub enum PortGrouping {
    Singleton(PortKind),
    Partition(Vec<PortKind>),
}

impl PortGrouping {
    pub fn flatten(&self) -> Vec<PortKind> {
        match self {
            Self::Singleton(p) => vec![p.clone()],
            Self::Partition(ps) => ps.clone(),
        }
    }

    pub fn as_singleton(&self) -> Option<&PortKind> {
        match &self {
            Self::Singleton(p) => Some(p),
            _ => None,
        }
    }
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

#[derive(Serialize, Deserialize, Ord, PartialOrd, Hash, Eq, Clone, Debug, PartialEq)]
pub enum PortKind {
    Input(Type),
    Output(Type),
}

impl PortKind {
    pub fn is_complement(&self, other: &PortKind) -> bool {
        match (self, other) {
            (Self::Input(ty_a), Self::Output(ty_b)) | (Self::Output(ty_b), Self::Input(ty_a)) => {
                ty_a == ty_b
            }
            _ => false,
        }
    }

    pub fn as_output(&self) -> Option<&Type> {
        match &self {
            Self::Input(_) => None,
            Self::Output(o) => Some(o),
        }
    }

    pub fn into_output(self) -> Option<Type> {
        match self {
            Self::Input(_) => None,
            Self::Output(o) => Some(o),
        }
    }

    pub fn as_input(&self) -> Option<&Type> {
        match &self {
            Self::Input(i) => Some(i),
            Self::Output(_) => None,
        }
    }
}

impl fmt::Display for PortKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Input(ty) => write!(f, "{}-", ty.0),
            Self::Output(ty) => write!(f, "{}+", ty.0),
        }
    }
}

#[derive(Serialize, Deserialize, Ord, PartialOrd, Hash, Eq, Clone, Debug, PartialEq)]
pub enum Port {
    Agent(Agent),
    Var(Ident),
}

impl Port {
    pub fn name(&self) -> Ident {
        match &self {
            Self::Agent(a) => Ident(a.name.0.clone()),
            Self::Var(i) => i.clone(),
        }
    }

    pub fn as_var(&self) -> Option<&Ident> {
        match &self {
            Self::Agent(_) => None,
            Self::Var(v) => Some(v),
        }
    }

    pub fn as_agent(&self) -> Option<&Agent> {
        match &self {
            Self::Agent(a) => Some(a),
            Self::Var(_) => None,
        }
    }

    pub fn into_agent(self) -> Option<Agent> {
        match self {
            Self::Agent(a) => Some(a),
            Self::Var(_) => None,
        }
    }
}

impl fmt::Display for Port {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Agent(a) => write!(f, "{}", a),
            Self::Var(v) => write!(f, "{}", v.0),
        }
    }
}
