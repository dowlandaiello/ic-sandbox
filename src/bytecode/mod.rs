use crate::{
    heuristics::TypedProgram,
    parser::ast_lafont::{Agent, Port, PortKind, Type},
    BYTECODE_INDENTATION_STR,
};
use serde::{Deserialize, Serialize};
use std::{
    collections::{BTreeMap, HashSet},
    fmt, iter,
};

pub mod vm;

pub type Ptr = usize;

#[derive(Debug, Serialize, Deserialize, Ord, PartialOrd, Eq, PartialEq)]
pub struct TypeSignature {
    pub ty: Type,
    pub ports: Vec<PortKind>,
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

#[derive(Debug, Default, Serialize, Deserialize)]
pub struct Program {
    pub names: Vec<Type>,

    pub symbol_declarations_for: BTreeMap<Type, Vec<PortKind>>,

    // Mapping from output agent to its reduction strategy
    pub reductions: BTreeMap<(Agent, Agent), Vec<Op>>,

    // Output elems of all active pairs
    pub active_pairs: Vec<(Option<Agent>, Option<Agent>)>,
}

impl Program {
    pub fn type_signature_for(&self, a: &Agent) -> Option<TypeSignature> {
        self.symbol_declarations_for
            .get(&a.name)
            .as_ref()
            .map(|ports| TypeSignature {
                ty: a.name.clone(),
                ports: (*ports).clone(),
            })
    }
}

impl fmt::Display for Program {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "names:\n{}\n\ntypes:\n{}\n\nreductions:\n{}\n\nactive_pairs:\n{}",
            self.names
                .iter()
                .map(|name| format!("{}{}", BYTECODE_INDENTATION_STR, name.0))
                .collect::<Vec<_>>()
                .join(&format!("{}\n", BYTECODE_INDENTATION_STR)),
            self.symbol_declarations_for
                .iter()
                .map(|(ty, ports)| format!(
                    "{}{}: {}",
                    BYTECODE_INDENTATION_STR,
                    ty,
                    ports
                        .iter()
                        .map(|p| p.to_string())
                        .collect::<Vec<_>>()
                        .join(", ")
                ))
                .collect::<Vec<_>>()
                .join("\n"),
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
                .map(|(a, b)| format!(
                    "{}{} >< {}",
                    BYTECODE_INDENTATION_STR,
                    a.as_ref().map(|a| a.to_string()).unwrap_or_default(),
                    b.as_ref().map(|b| b.to_string()).unwrap_or_default()
                ))
                .collect::<Vec<_>>()
                .join("\n")
        )
    }
}

/// Reductions are run with a pointer to a NetBuffer representing the
/// active redex in stack position #0.
///
/// Elements in the stack can either be pointers, instructions, or None
/// pointers can be to nets, or nodes in nets (variables or agents)
#[derive(Debug, PartialEq, Clone, Serialize, Deserialize)]
pub enum Op {
    /// Pushes a pointer to a new initialized net buffer to the stack
    PushPtrInitNet,

    /// Pushes a pointer to a copy of a net, as a net buffer to the stack
    PushPtrCpyNet(Ptr),

    Pop,

    /// Pushes a new node with a name given by the pointer
    /// to the net and a primary port given by the pointer
    /// Primary port must be known at compile time
    PushNodeVar(Ptr, Ptr),

    /// Pushes a new node with a name given by the pointer,
    /// in nodes given by the pointers,
    /// and out nodes given by the pointers
    PushNodeAgent(Ptr),

    /// Connects two nodes
    PushConn(Ptr, Ptr),

    /// This instruction stores whatever net is currently in the stack
    /// in the evaluations record for the call signature
    StoreResult,

    PushInstr(Box<Op>),

    /// Executes the first instruction in the stack (#1) if the condition (#0) is true
    /// otherwise executes the second (#3).
    CondExec,

    /// Pushes to the stack whether the first two elements in the stack
    /// are equivalent.
    PushEq,
    PushNeq,

    /// Pushes to the stack whether the element in the stack is None
    PushNone,
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
            Self::PushNodeVar(name, primary_port) => {
                write!(f, "PUSHB_V {} {}", name, primary_port)
            }
            Self::PushNodeAgent(name) => write!(f, "PUSHB_A {}", name),
            Self::PushConn(a, b) => write!(f, "PUSHC {} {}", a, b),
            Self::PushPtrCpyNet(ptr) => write!(f, "PUSHCPY_N {}", ptr),
        }
    }
}

/// If a net has no further active pairs to reduced, then it is terminal
/// and its result can be committed to the store.
///
/// Nodes to be committed are output nodes connected to output ports
fn try_amortize<'a>(
    names: &[Type],
    typings: &'a TypedProgram,
    lhs: Option<&'a Agent>,
    rhs: Option<&'a Agent>,
) -> Option<Vec<Op>> {
    fn amortize_from<'a>(
        names: &[Type],
        typings: &'a TypedProgram,
        output_agent: &'a Agent,
    ) -> Vec<Op> {
        let terminal_ports = typings.terminal_ports_for(output_agent);

        tracing::debug!(
            "agent {} has terminal port {:?}",
            output_agent,
            terminal_ports,
        );

        let mut ops = Vec::default();

        ops.extend(terminal_ports.into_iter().filter_map(|p| match p {
            Port::Agent(a) => {
                let name_ptr = names.iter().position(|name| name.0 == a.name.0)?;

                Some(Op::PushNodeAgent(name_ptr))
            }
            Port::Var(_) => None,
        }));

        ops
    }

    let mut ops = lhs
        .map(|lhs| amortize_from(names, typings, lhs))
        .unwrap_or_default();
    ops.extend(
        rhs.map(|rhs| amortize_from(names, typings, rhs))
            .unwrap_or_default(),
    );

    if ops.is_empty() {
        return None;
    }

    Some(ops)
}

/// A strategy that is a noop. Just copies the net to a buffer.
fn reduction_strategy_copy(net: Ptr) -> Vec<Op> {
    vec![Op::PushPtrCpyNet(net)]
}

/// Reduction is repeated replacing and result storing:
/// - Replacing is replacing variables, in all places they occur, with other values
/// - Result storing is the commitment of fully reduced terms, which commits
/// a fully reduced net to the store to skip further evaluation.
fn reduction_strategy(
    names: &[Type],
    typings: &TypedProgram,
    lhs: Option<&Agent>,
    rhs: Option<&Agent>,
    net_ptr: Ptr,
) -> Vec<Op> {
    tracing::debug!(
        "calculating reduction strategy for redex {} >< {}",
        lhs.as_ref()
            .map(|agent| agent.to_string())
            .unwrap_or_default(),
        rhs.as_ref()
            .map(|agent| agent.to_string())
            .unwrap_or_default()
    );

    if let Some(amortized_plan) = try_amortize(names, typings, lhs, rhs) {
        tracing::debug!(
            "redex {} >< {} is amortizable",
            lhs.as_ref()
                .map(|agent| agent.to_string())
                .unwrap_or_default(),
            rhs.as_ref()
                .map(|agent| agent.to_string())
                .unwrap_or_default()
        );

        return iter::once(Op::PushPtrInitNet)
            .chain(amortized_plan.into_iter())
            .chain(iter::once(Op::StoreResult))
            .collect();
    }

    reduction_strategy_copy(net_ptr)
        .into_iter()
        .chain(iter::once(Op::StoreResult))
        .collect()
}

pub fn compile(program: TypedProgram) -> Program {
    let names_iter = program
        .types
        .iter()
        .chain(program.symbol_declarations_for.iter().map(|(k, _)| k))
        .cloned()
        .chain(program.nets.iter().map(|n| n.names_mentioned()).flatten());

    let mut unique_names: HashSet<Type> = HashSet::default();

    let names = names_iter.fold(Vec::default(), |mut acc, x| {
        if unique_names.contains(&x) {
            return acc;
        }

        unique_names.insert(x.clone());
        acc.push(x);

        acc
    });

    let reductions = BTreeMap::from_iter(
        program
            .nets
            .iter()
            .enumerate()
            .map(|(i, net)| (i, net.lhs.as_ref(), net.rhs.as_ref()))
            .filter_map(|(ptr, lhs, rhs)| {
                Some((
                    (lhs?.clone(), rhs?.clone()),
                    reduction_strategy(&names, &program, lhs, rhs, ptr),
                ))
            }),
    );
    let active_pairs = program
        .nets
        .iter()
        .map(|net| (net.lhs.clone(), net.rhs.clone()))
        .collect::<Vec<_>>();

    Program {
        names,
        reductions,
        active_pairs,
        symbol_declarations_for: program.symbol_declarations_for,
    }
}
