use super::{CallSignature, Op, Program, Ptr};
use crate::{
    heuristics::TypedProgram,
    parser::ast_lafont::{Agent, Net, PortKind},
};
use std::collections::{linked_list::LinkedList, BTreeMap, HashSet};

#[derive(Debug, PartialEq)]
pub enum StackElem {
    Ptr(Ptr),
    None,
    Instr(Op),
    Bool(bool),
}

impl StackElem {
    pub fn as_ptr(&self) -> Option<&Ptr> {
        match &self {
            Self::Ptr(p) => Some(p),
            _ => None,
        }
    }

    pub fn into_ptr(self) -> Option<Ptr> {
        match self {
            Self::Ptr(p) => Some(p),
            _ => None,
        }
    }

    pub fn as_instr(&self) -> Option<&Op> {
        match &self {
            Self::Instr(instr) => Some(instr),
            _ => None,
        }
    }

    pub fn into_instr(self) -> Option<Op> {
        match self {
            Self::Instr(instr) => Some(instr),
            _ => None,
        }
    }

    pub fn as_bool(&self) -> Option<&bool> {
        match self {
            Self::Bool(b) => Some(b),
            _ => None,
        }
    }
}

#[derive(Debug, Clone)]
pub enum Node {
    /// In ports is a vec of pointers to variables or agents
    /// which the agent is connected to via input
    ///
    /// output_port_agents is a vec of pointers to agents
    /// which the variable or agent is connected to via output
    Agent {
        name: Ptr,
        in_ports: Vec<Ptr>,
        out_port_agents: Vec<Ptr>,
    },

    /// Primary port is a pointer to the agent which the variable
    /// is connected to by output
    Var { name: Ptr, primary_port: Ptr },
}

#[derive(Debug, Default, Clone)]
pub struct NetBuffer {
    pub nodes: Vec<Node>,
}

#[derive(Debug)]
pub struct ReductionFrame {
    pub stack: LinkedList<StackElem>,
    pub nets: Vec<NetBuffer>,
    pub call_signature: CallSignature,
}

/// An executor executes reduction steps on a program.
/// It attempts reduction on any
#[derive(Debug)]
pub struct Executor {
    // Hash of all input ports to an output agent, and their output
    // Gets added to as reductions are executed
    // TODO: implement this as an LRU cache
    pub evaluations: BTreeMap<CallSignature, NetBuffer>,

    pub p: Program,

    pub reduction: Option<ReductionFrame>,
}

impl Executor {
    pub fn new(p: Program) -> Self {
        Self {
            evaluations: Default::default(),
            p,
            reduction: Default::default(),
        }
    }

    /// Creates a new reduction frame with a call signature equal
    /// to the specified redex.
    ///
    /// Attributes of reduction known at compile time:
    /// - Type signature of call
    /// - Arguments of call
    /// - Reduction algorithms for "subproblems"
    /// - Subproblems can also be identified
    ///
    /// Reduction is, in essence, just repeated variable replacement
    /// on subproblems
    ///
    /// Reduction terminates when the output of a top-level redex
    /// is terminal (i.e., it does not contain any other redexs within
    /// it)
    pub fn new_reduction_frame(&self, lhs: &Agent, rhs: &Agent) -> Option<ReductionFrame> {
        let ty_lhs = self.p.symbol_declarations_for.get(&lhs.name)?;
        let ty_rhs = self.p.symbol_declarations_for.get(&lhs.name)?;

        let primary_port_lhs = ty_lhs.get(0).and_then(|arg| arg.as_singleton())?;
        let primary_port_rhs = ty_rhs.get(0).and_then(|arg| arg.as_singleton())?;

        // Whichever agent has a primary port being an input, we will
        // get its call signature (defined by the hash of all its input ports)
        //
        // TODO: PortGrouping support?
        let sig = match (primary_port_lhs, primary_port_rhs) {
            (&PortKind::Input(_), &PortKind::Output(_)) => Some(CallSignature::instantiate(
                lhs.name.clone(),
                ty_lhs
                    .iter()
                    .zip(lhs.ports.iter())
                    .filter(|(ty, _)| ty.as_singleton().and_then(|s| s.as_input()).is_some())
                    .map(|(_, val)| val.clone())
                    .collect::<Vec<_>>(),
            )),
            (&PortKind::Output(_), &PortKind::Input(_)) => Some(CallSignature::instantiate(
                rhs.name.clone(),
                ty_rhs
                    .iter()
                    .zip(rhs.ports.iter())
                    .filter(|(ty, _)| ty.as_singleton().and_then(|s| s.as_input()).is_some())
                    .map(|(_, val)| val.clone())
                    .collect::<Vec<_>>(),
            )),
            _ => None,
        };

        Some(ReductionFrame {
            stack: Default::default(),
            nets: Default::default(),
            call_signature: sig?,
        })
    }

    pub fn exec(&mut self, op: Op) {
        let frame = if let Some(v) = self.reduction.as_mut() {
            v
        } else {
            return;
        };

        match op {
            Op::PushPtrInitNet => {
                frame.nets.push(Default::default());
                let new_net_id = frame.nets.len() - 1;

                frame.stack.push_back(StackElem::Ptr(new_net_id));
            }
            Op::Pop => {
                frame.stack.pop_back();
            }
            Op::StoreResult => {
                let res_net = if let Some(res_net) = frame
                    .stack
                    .pop_back()
                    .and_then(|elem| elem.into_ptr())
                    .and_then(|id| frame.nets.get(id))
                {
                    res_net
                } else {
                    return;
                };

                self.evaluations
                    .insert(frame.call_signature.clone(), res_net.clone());
            }
            Op::PushInstr(op) => {
                frame.stack.push_back(StackElem::Instr(*op));
            }
            Op::CondExec => {
                if let Some((cmp, (Some(exec_true), Some(exec_false)))) = frame
                    .stack
                    .pop_back()
                    .and_then(|maybe_cond| maybe_cond.as_bool().copied())
                    .zip(
                        frame
                            .stack
                            .pop_back()
                            .map(|maybe_op_true| maybe_op_true.as_instr().cloned())
                            .zip(
                                frame
                                    .stack
                                    .pop_back()
                                    .map(|maybe_op_false| maybe_op_false.as_instr().cloned()),
                            ),
                    )
                {
                    if cmp {
                        self.exec(exec_true);
                    } else {
                        self.exec(exec_false);
                    }
                }
            }
            Op::PushEq => {
                if let Some((cmp_a, cmp_b)) = frame.stack.pop_back().zip(frame.stack.pop_back()) {
                    frame.stack.push_back(StackElem::Bool(cmp_a == cmp_b));
                }
            }
            Op::PushNeq => {
                if let Some((cmp_a, cmp_b)) = frame.stack.pop_back().zip(frame.stack.pop_back()) {
                    frame.stack.push_back(StackElem::Bool(cmp_a != cmp_b));
                }
            }
            Op::PushNone => {
                if let Some(cmp_a) = frame.stack.pop_back() {
                    frame
                        .stack
                        .push_back(StackElem::Bool(cmp_a == StackElem::None));
                }
            }
        }
    }

    /// Converts the program to a human-readable form
    pub fn readback(&self) -> TypedProgram {
        TypedProgram {
            types: self
                .p
                .reductions
                .iter()
                .fold(Default::default(), |mut acc, ((lhs, rhs), _)| {
                    acc.insert(lhs.ty.clone());
                    acc.insert(rhs.ty.clone());

                    acc
                }),
            symbol_declarations_for: self.p.reductions.iter().fold(
                Default::default(),
                |mut acc, ((lhs, rhs), _)| {
                    acc.insert(lhs.ty.clone(), lhs.ports.clone());
                    acc.insert(rhs.ty.clone(), rhs.ports.clone());

                    acc
                },
            ),
            nets: self
                .p
                .active_pairs
                .iter()
                .map(|(lhs, rhs)| Net {
                    lhs: Some(lhs.clone()),
                    rhs: Some(rhs.clone()),
                })
                .collect::<HashSet<_>>(),
        }
    }

    /// Steps the virtual machine until nothing in the stack is left to execute
    pub fn step_to_end(&mut self) {
        while self
            .reduction
            .as_ref()
            .map(|r| !r.stack.is_empty())
            .unwrap_or_default()
        {
            self.step();
        }
    }

    /// Attempts to reduce the next redex which has a redex in the rulebook
    /// to reduce it
    pub fn step(&mut self) {
        // Check if we have a rule to reduce the redex
        if let Some(((a, b), reduction)) = self
            .p
            .active_pairs
            .iter()
            .filter_map(|(a, b)| {
                self.p
                    .reductions
                    .get(&(
                        self.p.type_signature_for(&a)?,
                        self.p.type_signature_for(&b)?,
                    ))
                    .map(|reduction| ((a, b), reduction))
            })
            .next()
        {
            self.reduction = self.new_reduction_frame(a, b);

            // Attempt to execute the reduction for this active pair
            let ops = reduction.clone();

            for op in ops.into_iter() {
                self.exec(op);
            }
        }
    }
}
