use serde::{Deserialize, Serialize};

pub mod compilation;
pub mod vm;

pub type Ptr = usize;

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

#[derive(Ord, PartialEq, PartialOrd, Eq, Clone, Debug, Serialize, Deserialize)]
pub enum StackElem {
    Ident(String),
    Agent(Agent),
    Var(Ptr),
    Ptr(GlobalPtr),
    Instr(Box<Op>),
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
