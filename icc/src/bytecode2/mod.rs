use serde::{Deserialize, Serialize};
use std::fmt;

pub mod compilation;
pub mod vm;

pub type Ptr = usize;

#[derive(Serialize, Deserialize, Clone, Debug, Eq, PartialEq)]
pub struct Program(pub(crate) Vec<StackElem>);

impl Program {
    pub fn get(&self, pos: Ptr) -> Option<&StackElem> {
        self.0.get(pos)
    }

    pub fn push(&mut self, elem: StackElem) {
        self.0.push(elem)
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }
}

impl fmt::Display for Program {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}",
            self.0
                .iter()
                .map(|elem| elem.to_string())
                .collect::<Vec<_>>()
                .join("\n")
        )
    }
}

#[derive(Hash, Ord, PartialOrd, PartialEq, Eq, Copy, Clone, Debug, Serialize, Deserialize)]
pub enum GlobalPtr {
    StackPtr(Ptr),
    AgentPtr(AgentPtr),
}

impl fmt::Display for GlobalPtr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::StackPtr(p) => write!(f, "PSTACK {}", p),
            Self::AgentPtr(p) => write!(f, "PAGENT {}", p),
        }
    }
}

impl GlobalPtr {
    pub fn as_stack_ptr(&self) -> Option<Ptr> {
        match self {
            Self::StackPtr(p) => Some(*p),
            _ => None,
        }
    }
}

#[derive(Hash, Ord, PartialOrd, PartialEq, Eq, Copy, Clone, Debug, Serialize, Deserialize)]
pub struct AgentPtr {
    pub stack_pos: Ptr,
    pub port: Ptr,
}

impl fmt::Display for AgentPtr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "PSTACK {}, {}", self.stack_pos, self.port)
    }
}

#[derive(Ord, PartialEq, PartialOrd, Eq, Clone, Debug, Serialize, Deserialize)]
pub enum StackElem {
    Ident(String),
    Agent(Agent),
    Var(Ptr),
    Ptr(GlobalPtr),
    Instr(Box<Op>),
}

impl fmt::Display for StackElem {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Ident(name) => write!(f, "IDENT {}", name),
            Self::Agent(a) => write!(
                f,
                "AGENT {} {}",
                a.name,
                a.ports
                    .iter()
                    .map(|p| p.to_string())
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
            Self::Var(p) => write!(f, "VAR {}", p),
            Self::Ptr(p) => write!(f, "PTR {}", p),
            Self::Instr(op) => write!(f, "OP {}", op),
        }
    }
}

impl StackElem {
    pub fn as_agent_mut(&mut self) -> Option<&mut Agent> {
        match self {
            Self::Agent(a) => Some(a),
            _ => None,
        }
    }

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

impl Agent {
    pub fn push_port(&mut self, p: GlobalPtr) {
        self.ports.push(p)
    }
}

#[derive(Ord, PartialEq, PartialOrd, Eq, Clone, Debug, Serialize, Deserialize)]
pub enum Op {
    PushStackElem(StackElem),
    PushRes(GlobalPtr),
}

impl fmt::Display for Op {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::PushStackElem(elem) => write!(f, "PUSH_ELEM {}", elem),
            Self::PushRes(ptr) => write!(f, "PUSH_RES {}", ptr),
        }
    }
}
