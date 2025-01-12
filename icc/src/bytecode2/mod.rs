use serde::{Deserialize, Serialize};
use std::fmt;

pub mod compilation;
pub mod vm;

pub type Ptr = usize;
pub type Offset = isize;

#[derive(Default, Serialize, Deserialize, Clone, Debug, Eq, PartialEq)]
pub struct Program(pub(crate) Vec<StackElem>);

impl Program {
    pub fn get(&self, pos: Ptr) -> Option<&StackElem> {
        self.0.get(pos)
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

#[derive(Ord, PartialOrd, PartialEq, Eq, Copy, Clone, Debug, Serialize, Deserialize)]
pub enum GlobalPtr {
    MemPtr(Ptr),
    AgentPtr(AgentPtr),
    Offset(Offset),
}

impl fmt::Display for GlobalPtr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::MemPtr(p) => write!(f, "*{}", p),
            Self::AgentPtr(p) => write!(f, "A*{}", p),
            Self::Offset(o) => write!(f, "+{}", o),
        }
    }
}

impl GlobalPtr {
    pub fn as_agent_ptr(&self) -> Option<&AgentPtr> {
        match &self {
            Self::AgentPtr(p) => Some(p),
            _ => None,
        }
    }

    pub fn into_mem_ptr(self) -> Option<Ptr> {
        match self {
            Self::MemPtr(p) => Some(p),
            _ => None,
        }
    }

    pub fn into_agent_ptr(self) -> Option<AgentPtr> {
        match self {
            Self::AgentPtr(p) => Some(p),
            _ => None,
        }
    }

    pub fn add_offset(&self, offset: Offset) -> Option<Self> {
        Some(match self {
            Self::AgentPtr(AgentPtr { mem_pos, port }) => Self::AgentPtr(AgentPtr {
                mem_pos: *mem_pos,
                port: port
                    .map(|p| p.checked_add_signed(offset))
                    .unwrap_or(usize::try_from(offset - 1).ok()),
            }),
            Self::MemPtr(abs_ptr) => Self::MemPtr(abs_ptr.checked_add_signed(offset)?),
            Self::Offset(o) => Self::Offset(o + offset),
        })
    }

    pub fn as_mem_ptr(&self) -> Option<Ptr> {
        match self {
            Self::MemPtr(p) => Some(*p),
            _ => None,
        }
    }
}

#[derive(Ord, PartialOrd, PartialEq, Eq, Copy, Clone, Debug, Serialize, Deserialize)]
pub struct AgentPtr {
    pub mem_pos: Ptr,
    pub port: Option<Ptr>,
}

impl fmt::Display for AgentPtr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "PSTACK {}, {}",
            self.mem_pos,
            self.port
                .map(|p| p.to_string())
                .unwrap_or(String::from("NULL"))
        )
    }
}

#[derive(Ord, PartialEq, PartialOrd, Eq, Clone, Debug, Serialize, Deserialize)]
pub enum StackElem {
    Ident(String),
    Agent(Agent),
    Var(Ptr),
    Ptr(GlobalPtr),
    Instr(Box<Op>),
    Bool(bool),
    Offset(Offset),
    Num(usize),
    None,
}

impl From<Op> for StackElem {
    fn from(o: Op) -> Self {
        Self::Instr(Box::new(o))
    }
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
            Self::Bool(b) => write!(f, "BOOL {}", b),
            Self::None => write!(f, "NONE"),
            Self::Offset(o) => write!(f, "OFFSET {}", o),
            Self::Num(n) => write!(f, "NUM {}", n),
        }
    }
}

impl StackElem {
    pub fn into_op(self) -> Option<Op> {
        match self {
            Self::Instr(op) => Some(*op),
            _ => None,
        }
    }

    pub fn as_agent_mut(&mut self) -> Option<&mut Agent> {
        match self {
            Self::Agent(a) => Some(a),
            _ => None,
        }
    }

    pub fn into_agent(self) -> Option<Agent> {
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

    pub fn as_ptr(&self) -> Option<&GlobalPtr> {
        match &self {
            Self::Ptr(p) => Some(p),
            _ => None,
        }
    }

    pub fn into_ptr(self) -> Option<GlobalPtr> {
        match self {
            Self::Ptr(p) => Some(p),
            _ => None,
        }
    }

    pub fn as_offset(&self) -> Option<&Offset> {
        match &self {
            Self::Offset(o) => Some(o),
            _ => None,
        }
    }

    pub fn into_offset(self) -> Option<Offset> {
        match self {
            Self::Offset(o) => Some(o),
            _ => None,
        }
    }

    pub fn as_ptr_mut(&mut self) -> Option<&mut GlobalPtr> {
        match self {
            Self::Ptr(p) => Some(p),
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
    Load,
    LoadMem,
    PushStack(StackElem),
    PushRes,
    Debug,
    DebugMem,
    Cmp,
    GoTo,
    StoreAt,
    Deref,
    PortPtr,
    CondExec,
    GoToEq,
    GoToNeq,
    IncrPtr,
    Copy,
    RefIndex,
    PushRedex,
    QueueRedex,
    PushMatchingRule,
    CloneNet,
    PushSubstitutionPositions,
    Substitute,
}

impl fmt::Display for Op {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Load => write!(f, "LOAD"),
            Self::LoadMem => write!(f, "LOAD_MEM"),
            Self::PushStack(elem) => write!(f, "PUSH_STACK {}", elem),
            Self::PushRes => write!(f, "PUSH_RES"),
            Self::Debug => write!(f, "DEBUG"),
            Self::DebugMem => write!(f, "DEBUG_MEM"),
            Self::Cmp => write!(f, "CMP"),
            Self::GoTo => write!(f, "GOTO"),
            Self::StoreAt => write!(f, "STO_AT"),
            Self::CondExec => write!(f, "COND_EXEC"),
            Self::GoToEq => write!(f, "GOTO_EQ"),
            Self::GoToNeq => write!(f, "GOTO_NEQ"),
            Self::Deref => write!(f, "DEREF"),
            Self::PortPtr => write!(f, "PORT_NUM"),
            Self::IncrPtr => write!(f, "INCR_PTR"),
            Self::Copy => write!(f, "COPY"),
            Self::RefIndex => write!(f, "REF_INDEX"),
            Self::PushRedex => write!(f, "PUSH_REDEX"),
            Self::PushMatchingRule => write!(f, "PUSH_RULE"),
            Self::CloneNet => write!(f, "CLONE_NET"),
            Self::PushSubstitutionPositions => write!(f, "PUSH_SUB_POS"),
            Self::Substitute => write!(f, "SUB"),
            Self::QueueRedex => write!(f, "QUEUE_REDEX"),
        }
    }
}
