use super::parser::ast::{Instance, Rule};
use serde::{Deserialize, Serialize};
use std::{collections::BTreeMap, fmt};

type Ptr = usize;

#[derive(Serialize, Deserialize)]
pub enum Node {
    Var(Ptr),
    Agent { name: Ptr, ports: Vec<Ptr> },
}

/// Programs represent a plan for reducing a single active
/// pair which may correspond with some given rules.
/// Programs are a declaractive representation of how
/// an executor would execute the "plan."
#[derive(Default, Serialize, Deserialize)]
pub struct Program {
    pub names: Vec<String>,
    pub rules: BTreeMap<(Ptr, Ptr), Vec<Op>>,
    pub instance: Net,
}

impl Program {
    /// Inserts an identifier in the program, registering it
    /// if it does not exist. Does not insert any new nodes.
    pub fn push_name(&mut self, name: String) -> usize {
        self.names
            .iter()
            .position(|maybe_name| *maybe_name == *name)
            .unwrap_or_else(|| {
                self.names.push(name);
                self.names.len() - 1
            })
    }
}

#[derive(Default, Serialize, Deserialize)]
pub struct Net {
    pub nodes: Vec<Node>,
}

impl Net {
    /// Inserts the node. Nodes do not necessarily have to be unique.
    /// Assumes the name being referenced to has already
    /// been inserted.
    pub fn push_node(&mut self, n: Node) -> Ptr {
        self.nodes.push(n);

        self.nodes.len() - 1
    }
}

#[derive(Serialize, Deserialize)]
pub enum Op {
    Copy {
        node: Ptr,
        src_net: Ptr,
        dest_net: Ptr,
    },

    Connect {
        src_node: Ptr,
        dest_node: Ptr,
    },
}

impl fmt::Display for Op {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Copy {
                src_net,
                node,
                dest_net,
            } => write!(f, "CP {} {} {}", node, src_net, dest_net),
            Self::Connect {
                src_node,
                dest_node,
            } => write!(f, "CN {} {}", src_node, dest_node),
        }
    }
}

pub fn compile(_rules: Vec<Rule>, _instance: Instance) -> Program {
    todo!()
}
