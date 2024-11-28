use crate::{
    heuristics::TypedProgram,
    parser::ast_lafont::{Agent, Port, PortGrouping, PortKind, Type},
    BYTECODE_INDENTATION_STR,
};
use serde::{Deserialize, Serialize};
use std::{
    collections::{BTreeMap, HashSet},
    fmt,
    hash::{DefaultHasher, Hash, Hasher},
};

pub mod vm;

pub type Ptr = usize;

#[derive(Debug, Serialize, Deserialize, Ord, PartialOrd, Eq, PartialEq)]
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

#[derive(Clone, Debug, Serialize, Deserialize, Ord, PartialOrd, Eq, PartialEq)]
pub struct CallSignature {
    pub ty: Type,
    pub in_ports_hash: u64,
}

impl CallSignature {
    pub fn instantiate(ty: Type, args: Vec<Port>) -> Self {
        let mut hasher = DefaultHasher::new();
        args.hash(&mut hasher);

        Self {
            ty,
            in_ports_hash: hasher.finish(),
        }
    }
}

#[derive(Debug, Default, Serialize, Deserialize)]
pub struct Program {
    pub names: Vec<Type>,

    pub symbol_declarations_for: BTreeMap<Type, Vec<PortGrouping>>,

    // Mapping from output agent to its reduction strategy
    pub reductions: BTreeMap<(TypeSignature, TypeSignature), Vec<Op>>,

    // Output elems of all active pairs
    pub active_pairs: Vec<(Agent, Agent)>,
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

/// Reductions are run with a pointer to a NetBuffer representing the
/// active redex in stack position #0.
///
/// Elements in the stack can either be pointers, instructions, or None
/// pointers can be to nets, or nodes in nets (variables or agents)
#[derive(Debug, PartialEq, Clone, Serialize, Deserialize)]
pub enum Op {
    /// Pushes a pointer to a new initialized net buffer to the stack
    PushPtrInitNet,

    Pop,

    /// Pushes a new node with a name given by the pointer
    /// to the net and a primary port given by the pointer
    /// Primary port must be known at compile time
    PushNodeVar(Ptr, Ptr),

    /// Pushes a new node with a name given by the pointer,
    /// in nodes given by the pointers,
    /// and out nodes given by the pointers
    PushNodeAgent(Ptr),

    /// Connects two nodes by a +-+ conn
    PushConnOutOut(Ptr, Ptr),

    /// Connects two nodes by a +-- conn
    PushConnInOut(Ptr, Ptr),

    /// Connects two nodes by a --- conn
    PushConnInIn(Ptr, Ptr),

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
            Self::PushConnInIn(a, b) => write!(f, "PUSHC_II {} {}", a, b),
            Self::PushConnOutOut(a, b) => write!(f, "PUSHC_OO {} {}", a, b),
            Self::PushConnInOut(a, b) => write!(f, "PUSHC_IO {} {}", a, b),
        }
    }
}

/// If the output of a net is terminal (as in, its output is a variable or an output agent),
/// then its reduction is a simple call to StoreResult, after building the corresponding
/// netbuffer (can just copy it).
fn try_amortize<'a>(
    names: &[Type],
    typings: &'a TypedProgram,
    lhs: &'a Agent,
    rhs: &'a Agent,
) -> Option<Vec<Op>> {
    fn amortize_from<'a>(
        names: &[Type],
        typings: &'a TypedProgram,
        output_agent: &'a Agent,
    ) -> Option<Vec<Op>> {
        let terminal_port = typings.terminal_port_for(output_agent)?;

        // If we have a terminal port, that means we can amortize the output
        // to that terminal port's value
        let terminal_port_name_id = names.iter().position(|x| x.0 == terminal_port.0)?;

        tracing::debug!(
            "agent {} has terminal port {} (@{})",
            output_agent,
            terminal_port,
            terminal_port_name_id
        );

        Some(vec![
            // We aren't connected to anything, we are the output (gigachad)
            Op::PushPtrInitNet,
            Op::PushNodeAgent(terminal_port_name_id),
            Op::StoreResult,
        ])
    }

    amortize_from(names, typings, lhs).or_else(|| amortize_from(names, typings, rhs))
}

fn reduction_strategy(names: &[Type], typings: &TypedProgram, lhs: &Agent, rhs: &Agent) -> Vec<Op> {
    tracing::debug!(
        "calculating reduction strategy for redex {} >< {}",
        lhs,
        rhs
    );

    if let Some(amortized_plan) = try_amortize(names, typings, lhs, rhs) {
        tracing::debug!(
            "redex {} >< {} is amortizable:\n{}",
            lhs,
            rhs,
            amortized_plan
                .iter()
                .map(|s| format!("{}{}", BYTECODE_INDENTATION_STR, s))
                .collect::<Vec<_>>()
                .join("\n")
        );

        return amortized_plan;
    }

    vec![Op::PushPtrInitNet, Op::Pop]
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
                        reduction_strategy(&names, &program, lhs, rhs),
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
                        reduction_strategy(&names, &program, lhs, rhs),
                    ))
                } else {
                    None
                }
            }),
    );
    let active_pairs = program
        .nets
        .iter()
        .filter_map(|net| net.lhs.clone().zip(net.rhs.clone()))
        .collect::<Vec<_>>();

    Program {
        names,
        reductions,
        active_pairs,
        symbol_declarations_for: program.symbol_declarations_for,
    }
}
