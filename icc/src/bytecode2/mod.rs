use serde::{Deserialize, Serialize};
use std::fmt;

pub mod compilation;
pub mod vm;

pub type Ptr = usize;
pub type Offset = isize;

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
    Offset(Offset),
}

impl fmt::Display for GlobalPtr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::StackPtr(p) => write!(f, "*{}", p),
            Self::AgentPtr(p) => write!(f, "A*{}", p),
            Self::Offset(o) => write!(f, "+{}", o),
        }
    }
}

impl GlobalPtr {
    pub fn add_offset(&self, offset: Offset) -> Option<Self> {
        Some(match self {
            Self::AgentPtr(AgentPtr { stack_pos, port }) => Self::AgentPtr(AgentPtr {
                stack_pos: *stack_pos,
                port: port
                    .map(|p| p.checked_add_signed(offset))
                    .unwrap_or(usize::try_from(offset - 1).ok()),
            }),
            Self::StackPtr(abs_ptr) => Self::StackPtr(abs_ptr.checked_add_signed(offset)?),
            Self::Offset(o) => Self::Offset(o + offset),
        })
    }

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
    pub port: Option<Ptr>,
}

impl fmt::Display for AgentPtr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "PSTACK {}, {}",
            self.stack_pos,
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

    pub fn as_ptr(&self) -> Option<&GlobalPtr> {
        match &self {
            Self::Ptr(p) => Some(p),
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
    PushStackElem(StackElem),
    PushRes(GlobalPtr),
    Debug(GlobalPtr),
    Cmp(GlobalPtr, GlobalPtr),
    GoTo(Ptr),
    JumpBy(Offset),
    Store,
    Deref,
    CondExec,
    IncrPtrBy(Offset),
}

impl fmt::Display for Op {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::PushStackElem(elem) => write!(f, "PUSH_ELEM {}", elem),
            Self::PushRes(ptr) => write!(f, "PUSH_RES {}", ptr),
            Self::Debug(ptr) => write!(f, "DEBUG {}", ptr),
            Self::Cmp(a, b) => write!(f, "CMP {} {}", a, b),
            Self::GoTo(pos) => write!(f, "GOTO {}", pos),
            Self::JumpBy(diff) => write!(f, "JUMP_BY {}", diff),
            Self::Store => write!(f, "STO"),
            Self::CondExec => write!(f, "COND_EXEC"),
            Self::Deref => write!(f, "DEREF"),
            Self::IncrPtrBy(o) => write!(f, "INCR_PTR_BY {}", o),
        }
    }
}
