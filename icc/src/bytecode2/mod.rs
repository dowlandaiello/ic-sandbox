use serde::{Deserialize, Serialize};
use std::{error, fmt};

pub mod vm;

pub type Ptr = usize;

#[derive(Copy, Clone, Debug)]
pub enum Error {
    /// There are no instructions left to advance the machine with.
    NothingToAdvance,

    /// The machine failed to advance
    CouldNotAdvance,

    /// Ptr to a location that does not exist
    InvalidPtr,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::NothingToAdvance => write!(f, "nothing to advance"),
            Self::CouldNotAdvance => write!(f, "failed to advance"),
            Self::InvalidPtr => write!(f, "ptr out of bounds"),
        }
    }
}

impl error::Error for Error {}

#[derive(Ord, PartialOrd, PartialEq, Eq, Copy, Clone, Debug, Serialize, Deserialize)]
pub enum GlobalPtr {
    StackPtr(Ptr),
    AgentPtr(AgentPtr),
}

impl GlobalPtr {
    pub fn as_stack_ptr(&self) -> Option<Ptr> {
        match self {
            Self::StackPtr(p) => Some(*p),
            _ => None,
        }
    }
}

#[derive(Ord, PartialOrd, PartialEq, Eq, Copy, Clone, Debug, Serialize, Deserialize)]
pub struct AgentPtr {
    pub stack_pos: Ptr,
    pub port: Ptr,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum StackElem {
    Ident(String),
    Agent(Agent),
    Var(Ptr),
    Ptr(GlobalPtr),
    Instr(Box<Op>),
}

impl StackElem {
    pub fn as_agent(&self) -> Option<&Agent> {
        match &self {
            Self::Agent(a) => Some(a),
            _ => None,
        }
    }

    pub fn as_ident(&self) -> Option<&str> {
        match &self {
            Self::Ident(s) => Some(s),
            _ => None,
        }
    }
}

#[derive(Ord, PartialEq, PartialOrd, Eq, Clone, Debug, Serialize, Deserialize)]
pub struct Agent {
    pub name: GlobalPtr,
    pub ports: Vec<GlobalPtr>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum Op {
    PushStackElem(StackElem),
    Return(GlobalPtr),
}
