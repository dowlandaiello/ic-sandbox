use crate::{
    heuristics::TypedProgram,
    parser::ast_lafont::{Agent, Net, PortGrouping, PortKind, Type},
    BYTECODE_INDENTATION_STR,
};
use serde::{Deserialize, Serialize};
use std::{
    collections::{BTreeMap, BTreeSet},
    fmt,
};

pub type Ptr = usize;

#[derive(Serialize, Deserialize, Ord, PartialOrd, Eq, PartialEq)]
pub struct TypeSignature {
    pub ty: Type,
    pub ports: Vec<PortGrouping>,
}

impl fmt::Display for TypeSignature {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}({})",
            self.ty.0,
            self.ports
                .iter()
                .map(|p| p.to_string())
                .collect::<Vec<_>>()
                .join(", ")
        )
    }
}

#[derive(Serialize, Deserialize, Ord, PartialOrd, Eq, PartialEq)]
pub struct CallSignature {
    pub ty: Type,
    pub in_ports_hash: u64,
}

#[derive(Default, Serialize, Deserialize)]
pub struct Program {
    pub names: BTreeSet<Type>,

    // Hash of all input ports to an output agent, and their output
    pub evaluations: BTreeMap<CallSignature, Ptr>,

    // Mapping from output agent to its reduction strategy
    pub reductions: BTreeMap<(TypeSignature, TypeSignature), Vec<Op>>,

    // Output elems of all active pairs
    pub active_pairs: Vec<(Agent, Agent)>,
}

impl fmt::Display for Program {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "names:\n{}\n\nreductions:\n{}\n\nactive_pairs:\n{}",
            self.names
                .iter()
                .map(|name| format!("{}{}", BYTECODE_INDENTATION_STR, name.0))
                .collect::<Vec<_>>()
                .join(&format!("{}\n", BYTECODE_INDENTATION_STR)),
            self.reductions
                .iter()
                .map(|((signature_a, signature_b), ops)| format!(
                    "{}{} >< {}:\n{}",
                    BYTECODE_INDENTATION_STR,
                    signature_a,
                    signature_b,
                    ops.iter()
                        .map(|op| format!(
                            "{}{}{}",
                            BYTECODE_INDENTATION_STR,
                            BYTECODE_INDENTATION_STR,
                            op.to_string()
                        ))
                        .collect::<Vec<_>>()
                        .join("\n")
                ))
                .collect::<Vec<_>>()
                .join("\n\n"),
            self.active_pairs
                .iter()
                .map(|(a, b)| format!("{}{} >< {}", BYTECODE_INDENTATION_STR, a, b))
                .collect::<Vec<_>>()
                .join("\n")
        )
    }
}

/// Reductions are run with a pointer to the lhs agent
/// and rhs of a redex in the first and second stack positions, respectively.
/// Elements in the stack can either be pointers, instructions, or None
/// pointers can be to nets, or nodes in nets (variables or agents)
#[derive(Serialize, Deserialize)]
pub enum Op {
    /// Pushes a pointer to the initialized net to the stack
    PushPtrInitNet,

    Pop,

    /// This instruction stores whatever net is currently in the stack
    /// in the evaluations record for the call signature
    StoreResult,

    PushInstr(Box<Op>),

    /// Executes the first instruction in the stack (#1) if the condition (#0) is true
    /// otherwise executes the second (#3). Does not pop any elements.
    CondExec,

    /// Pushes to the stack whether the first two elements in the stack
    /// are equivalent. Does not pop the elements being compared
    PushEq,
    PushNeq,

    /// Pushes to the stack whether the element in the stack is None
    PushNone,

    /// Pushes a rule matching the agents in positions #0 and #1, respectively
    /// or pushes none
    PushMatchingRedexMaybe,
}

impl fmt::Display for Op {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::PushPtrInitNet => write!(f, "PUSH_INIT"),
            Self::Pop => write!(f, "POP"),
            Self::StoreResult => write!(f, "STORE_RES"),
            Self::PushInstr(op) => write!(f, "PUSH_INSTR {}", op),
            Self::CondExec => write!(f, "COND_EXEC"),
            Self::PushEq => write!(f, "PUSH_EQ"),
            Self::PushNeq => write!(f, "PUSH_NEQ"),
            Self::PushNone => write!(f, "PUSH_NONE"),
            Self::PushMatchingRedexMaybe => write!(f, "PUSH_REDEX_MAYBE"),
        }
    }
}

fn reduction_strategy(lhs: &Agent, rhs: &Agent) -> Vec<Op> {
    vec![
        Op::PushPtrInitNet,
        // If there is no matching rule in the rulebook,
        // give up and store the net, since it
        // is fully reduced, or as fully reduced as we can get it
        //
        // TODO: This could be a source of bugs. Can we imagine
        // a scenario in which we have no matching ruless and
        // where we don't want to store a result?
        Op::PushMatchingRedexMaybe,
        // Check if we have a matching redex
        Op::PushNone,
        // If we don't, store the result and terminate
        Op::PushInstr(Box::new(Op::StoreResult)),
        // Otherwise, stop the program
        Op::Pop,
    ]
}

pub fn compile(program: TypedProgram) -> Program {
    let mut p: Program = Default::default();

    p.names = BTreeSet::from_iter(
        program
            .types
            .iter()
            .chain(program.symbol_declarations_for.iter().map(|(k, _)| k))
            .cloned(),
    );
    p.reductions = BTreeMap::from_iter(
        program
            .nets
            .iter()
            .filter_map(|net| net.lhs.as_ref().zip(net.rhs.as_ref()))
            .filter_map(|(lhs, rhs)| {
                let ty_lhs = program.get_declaration_for(&lhs.name)?;
                let ty_rhs = program.get_declaration_for(&rhs.name)?;

                let primary_port_lhs = ty_lhs.get(0)?;
                let primary_port_rhs = ty_rhs.get(0)?;

                if let PortGrouping::Singleton(PortKind::Output(_)) = primary_port_lhs {
                    Some((
                        (
                            TypeSignature {
                                ty: lhs.name.clone(),
                                ports: ty_lhs.to_vec(),
                            },
                            TypeSignature {
                                ty: rhs.name.clone(),
                                ports: ty_rhs.to_vec(),
                            },
                        ),
                        reduction_strategy(lhs, rhs),
                    ))
                } else if let PortGrouping::Singleton(PortKind::Output(_)) = primary_port_rhs {
                    Some((
                        (
                            TypeSignature {
                                ty: rhs.name.clone(),
                                ports: ty_rhs.to_vec(),
                            },
                            TypeSignature {
                                ty: lhs.name.clone(),
                                ports: ty_lhs.to_vec(),
                            },
                        ),
                        reduction_strategy(lhs, rhs),
                    ))
                } else {
                    None
                }
            }),
    );
    p.active_pairs = program
        .nets
        .iter()
        .filter_map(|net| net.lhs.clone().zip(net.rhs.clone()))
        .collect::<Vec<_>>();

    p
}
