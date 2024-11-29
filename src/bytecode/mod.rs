use crate::{
    heuristics::TypedProgram,
    parser::ast_lafont::{Agent, Port, PortKind, Type},
    BYTECODE_INDENTATION_STR,
};
use serde::{Deserialize, Serialize};
use std::{
    collections::{BTreeMap, HashSet},
    fmt,
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

#[derive(Debug, PartialEq, Clone, Serialize, Deserialize)]
pub enum Op {
    /// Pushes a pointer to a new initialized net buffer to the stack
    PushPtrInitNet,

    /// Pushes a pointer to a copy of a net to the stack
    PushPtrCpyNet(Ptr),

    /// Copies an agent into the net buffer
    CutAgent(Agent),

    /// Renames all names to other names in the net
    Rename(Ptr, Port),

    Pop,

    /// This instruction stores whatever net is currently in the stack
    /// in the evaluations record for the call signature
    StoreResult,
}

impl fmt::Display for Op {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::PushPtrInitNet => write!(f, "PUSH_INIT"),
            Self::Pop => write!(f, "POP"),
            Self::StoreResult => write!(f, "STORE_RES"),
            Self::PushPtrCpyNet(ptr) => write!(f, "PUSHCPY_NET {}", ptr),
            Self::CutAgent(a) => write!(f, "CUT_AGENT {}", a.name),
            Self::Rename(src_ptr, dest_ptr) => write!(f, "RENAME {} {}", src_ptr, dest_ptr),
        }
    }
}

/// If a net has no further active pairs to reduced, then it is terminal
/// and its result can be committed to the store.
///
/// Nodes to be committed are output nodes connected to output ports
fn try_amortize<'a>(
    typings: &'a TypedProgram,
    lhs: Option<&'a Agent>,
    rhs: Option<&'a Agent>,
) -> Option<Vec<Op>> {
    fn amortize_from<'a>(typings: &'a TypedProgram, output_agent: &'a Agent) -> Vec<Op> {
        let type_dec = if let Some(typing) = typings.symbol_declarations_for.get(&output_agent.name)
        {
            typing.iter().cloned().skip(1).collect::<Vec<_>>()
        } else {
            return Default::default();
        };

        let terminal_ports = typings.terminal_ports_for(output_agent, &type_dec);

        tracing::debug!(
            "agent {} has terminal port {:?}",
            output_agent,
            terminal_ports,
        );

        let mut ops = Vec::default();

        ops.extend(terminal_ports.into_iter().filter_map(|p| match p {
            // TODO: Use references for this
            Port::Agent(a) => Some(Op::CutAgent(a.clone())),
            Port::Var(_) => None,
        }));

        ops
    }

    let mut ops = lhs
        .map(|lhs| amortize_from(typings, lhs))
        .unwrap_or_default();
    ops.extend(
        rhs.map(|rhs| amortize_from(typings, rhs))
            .unwrap_or_default(),
    );

    if ops.is_empty() {
        return None;
    }

    Some(ops)
}

fn try_infer<'a>(
    reductions: &BTreeMap<(Agent, Agent), Vec<Op>>,
    names: &Vec<Type>,
    lhs: &'a Agent,
    rhs: &'a Agent,
) -> Option<Vec<Op>> {
    let mut ops: Vec<Op> = Vec::default();
    let mut renamed = (lhs.clone(), rhs.clone());

    for ((a, b), reduction) in reductions.iter() {
        let bindings = a
            .subset_bindings(&mut renamed.0)
            .into_iter()
            .chain(b.subset_bindings(&mut renamed.1))
            .collect::<Vec<_>>();

        if !bindings.is_empty() {
            // This rule is a match. Replace variables in original
            // expression, then follow subproblem reduction
            // then replace again
            ops.extend(reduction.clone());

            for (var_ptr, replace) in bindings.into_iter().filter_map(|(var, replace)| {
                Some((names.iter().position(|x| x.0 == var.0)?, replace))
            }) {
                ops.push(Op::Rename(var_ptr, replace.clone()));
            }

            return Some(ops);
        }

        let bindings = a
            .subset_bindings(&mut renamed.0)
            .into_iter()
            .chain(b.subset_bindings(&mut renamed.1))
            .collect::<Vec<_>>();

        if !bindings.is_empty() {
            // This rule is a match. Replace variables in original
            // expression, then follow subproblem reduction
            // then replace again
            ops.extend(reduction.clone());

            for (var_ptr, replace) in bindings.into_iter().filter_map(|(var, replace)| {
                Some((names.iter().position(|x| x.0 == var.0)?, replace))
            }) {
                ops.push(Op::Rename(var_ptr, replace.clone()));
            }

            return Some(ops);
        }
    }

    // Replace

    None
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

    let to_reduce = program
        .nets
        .iter()
        .enumerate()
        .map(|(i, net)| (i, net.lhs.as_ref(), net.rhs.as_ref()));

    let amortizable_reductions =
        BTreeMap::from_iter(to_reduce.clone().filter_map(|(_, lhs, rhs)| {
            Some((
                (lhs?.clone(), rhs?.clone()),
                try_amortize(&program, lhs, rhs)?,
            ))
        }));
    let reductions = BTreeMap::from_iter(amortizable_reductions.clone().into_iter().chain(
        to_reduce.filter_map(|(_, lhs, rhs)| {
            Some((
                (lhs?.clone(), rhs?.clone()),
                try_infer(&amortizable_reductions, &names, lhs?, rhs?)?,
            ))
        }),
    ));

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
