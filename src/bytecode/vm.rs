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

impl Node {
    pub fn connect_in(self, other: Ptr) -> Self {
        match self {
            Self::Agent {
                name,
                mut in_ports,
                out_port_agents,
            } => {
                in_ports.push(other);

                Self::Agent {
                    name,
                    in_ports,
                    out_port_agents,
                }
            }
            Self::Var { .. } => self,
        }
    }

    pub fn connect_out(self, other: Ptr) -> Self {
        match self {
            Self::Agent {
                name,
                in_ports,
                mut out_port_agents,
            } => {
                out_port_agents.push(other);

                Self::Agent {
                    name,
                    in_ports,
                    out_port_agents,
                }
            }
            Self::Var { name, .. } => Self::Var {
                name,
                primary_port: other,
            },
        }
    }
}

#[derive(Debug, Default, Clone)]
pub struct NetBuffer {
    pub nodes: Vec<Node>,
}

#[derive(Debug)]
pub struct ReductionFrame {
    pub stack: LinkedList<StackElem>,
    pub instructions: LinkedList<Op>,
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

    pub fn call_signature_for(&self, lhs: &Agent, rhs: &Agent) -> Option<CallSignature> {
        let ty_lhs = self.p.symbol_declarations_for.get(&lhs.name)?;
        let ty_rhs = self.p.symbol_declarations_for.get(&lhs.name)?;

        let primary_port_lhs = ty_lhs.get(0).and_then(|arg| arg.as_singleton())?;
        let primary_port_rhs = ty_rhs.get(0).and_then(|arg| arg.as_singleton())?;

        // Whichever agent has a primary port being an input, we will
        // get its call signature (defined by the hash of all its input ports)
        //
        // TODO: PortGrouping support?
        match (primary_port_lhs, primary_port_rhs) {
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
    pub fn new_reduction_frame(
        &self,
        reduction: LinkedList<Op>,
        lhs: &Agent,
        rhs: &Agent,
    ) -> Option<ReductionFrame> {
        Some(ReductionFrame {
            instructions: reduction,
            stack: Default::default(),
            nets: Default::default(),
            call_signature: self.call_signature_for(lhs, rhs)?,
        })
    }

    pub fn step_frame(&mut self) {
        let frame = if let Some(v) = self.reduction.as_mut() {
            v
        } else {
            return;
        };

        let op = if let Some(op) = frame.instructions.pop_back() {
            op
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
                    frame
                        .instructions
                        .push_back(if cmp { exec_true } else { exec_false });

                    self.step_frame();
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
            // Continuously pop connect and create node instructions until we have created the net
            p @ Op::PushNodeVar(_, _)
            | p @ Op::PushNodeAgent(_)
            | p @ Op::PushConnOutOut(_, _)
            | p @ Op::PushConnInIn(_, _)
            | p @ Op::PushConnInOut(_, _) => {
                let n_ptr = if let Some(StackElem::Ptr(ptr)) = frame.stack.pop_back() {
                    ptr
                } else {
                    return;
                };

                // Will need to add nodes, conns, or vars to this
                let net = if let Some(net) = frame.nets.get_mut(n_ptr) {
                    net
                } else {
                    return;
                };

                match p {
                    Op::PushNodeVar(name_ptr, primary_port_ptr) => {
                        net.nodes.push(Node::Var {
                            name: name_ptr,
                            primary_port: primary_port_ptr,
                        });
                    }
                    Op::PushNodeAgent(name_ptr) => {
                        net.nodes.push(Node::Agent {
                            name: name_ptr,
                            in_ports: Default::default(),
                            out_port_agents: Default::default(),
                        });
                    }
                    Op::PushConnOutOut(a_ptr, b_ptr) => {
                        net.nodes[a_ptr] = net.nodes.remove(a_ptr).connect_out(b_ptr);
                        net.nodes[b_ptr] = net.nodes.remove(b_ptr).connect_out(a_ptr);
                    }
                    Op::PushConnInIn(a_ptr, b_ptr) => {
                        net.nodes[a_ptr] = net.nodes.remove(a_ptr).connect_in(b_ptr);
                        net.nodes[b_ptr] = net.nodes.remove(b_ptr).connect_in(a_ptr);
                    }
                    Op::PushConnInOut(a_ptr, b_ptr) => {
                        net.nodes[a_ptr] = net.nodes.remove(a_ptr).connect_in(b_ptr);
                        net.nodes[b_ptr] = net.nodes.remove(b_ptr).connect_out(a_ptr);
                    }
                    _ => {
                        unreachable!()
                    }
                }

                // We will need this for further operations, and for our outputresult
                frame.stack.push_back(StackElem::Ptr(n_ptr));
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
        // We are done once we have no results
        // left to evaluate
        loop {
            if let Some(next) = self
                .p
                .active_pairs
                .clone()
                .iter()
                .filter(|(a, b)| {
                    !self
                        .call_signature_for(a, b)
                        .map(|sig| self.evaluations.contains_key(&sig))
                        .unwrap_or_default()
                })
                .next()
            {
                self.step(&next);
            } else {
                break;
            }
        }
    }

    /// Attempts to reduce the next redex which has a redex in the rulebook
    /// to reduce it
    pub fn step(&mut self, redex: &(Agent, Agent)) {
        let (a, b) = redex;

        // Check if we have a rule to reduce the redex
        if let Some(reduction) = self
            .p
            .type_signature_for(&a)
            .zip(self.p.type_signature_for(&b))
            .and_then(|(sig_a, sig_b)| self.p.reductions.get(&(sig_a, sig_b)))
        {
            // Attempt to execute the reduction for this active pair
            self.reduction =
                self.new_reduction_frame(reduction.into_iter().cloned().collect(), a, b);

            while self
                .reduction
                .as_ref()
                .map(|r| !r.instructions.is_empty())
                .unwrap_or_default()
            {
                self.step_frame();
            }
        }
    }
}
