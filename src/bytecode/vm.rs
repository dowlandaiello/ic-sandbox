use super::{Op, Program, Ptr};
use crate::{
    heuristics::TypedProgram,
    parser::ast_lafont::{Agent, Ident, Net, Port, Type},
};
use std::collections::{linked_list::LinkedList, BTreeMap, BTreeSet};

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

#[derive(Debug, Copy, Clone)]
pub enum NodePort {
    In(Ptr),
    Out(Ptr),
}

impl NodePort {
    pub fn as_ptr(&self) -> Ptr {
        match self {
            Self::In(p) => *p,
            Self::Out(p) => *p,
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
    Agent { name: Ptr, ports: Vec<NodePort> },

    /// Primary port is a pointer to the agent which the variable
    /// is connected to by output
    Var { name: Ptr, primary_port: Ptr },
}

impl Node {
    pub fn connect_in(self, other: Ptr) -> Self {
        match self {
            Self::Agent { name, mut ports } => {
                ports.push(NodePort::In(other));

                Self::Agent { name, ports }
            }
            Self::Var { .. } => self,
        }
    }

    pub fn connect_out(self, other: Ptr) -> Self {
        match self {
            Self::Agent { name, mut ports } => {
                ports.push(NodePort::Out(other));

                Self::Agent { name, ports }
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
    pub active_pairs: Vec<(Ptr, Ptr)>,
}

#[derive(Debug)]
pub struct ReductionFrame {
    pub stack: LinkedList<StackElem>,
    pub instructions: LinkedList<Op>,
    pub nets: Vec<NetBuffer>,
    pub call_sig: (Agent, Agent),
}

impl ReductionFrame {
    pub fn new(instructions: LinkedList<Op>, call_sig: (Agent, Agent)) -> Self {
        Self {
            instructions,
            nets: Default::default(),
            stack: Default::default(),
            call_sig,
        }
    }
}

/// An executor executes reduction steps on a program.
/// It attempts reduction on any
#[derive(Debug)]
pub struct Executor {
    // Hash of all input ports to an output agent, and their output
    // Gets added to as reductions are executed
    // TODO: implement this as an LRU cache
    pub evaluations: BTreeMap<(Agent, Agent), NetBuffer>,

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

    pub fn step_frame(&mut self) -> Option<()> {
        let op = self.reduction.as_mut()?.instructions.pop_front()?;

        tracing::debug!("executing op {}", op);

        match op {
            Op::PushPtrInitNet => {
                self.reduction.as_mut()?.nets.push(Default::default());
                let new_net_id = self.reduction.as_ref()?.nets.len() - 1;

                self.reduction
                    .as_mut()?
                    .stack
                    .push_back(StackElem::Ptr(new_net_id));
            }
            Op::Pop => {
                self.reduction.as_mut()?.stack.pop_back();
            }
            Op::StoreResult => {
                let res_net = self
                    .reduction
                    .as_mut()?
                    .stack
                    .pop_back()
                    .and_then(|elem| elem.into_ptr())
                    .and_then(|id| self.reduction.as_ref()?.nets.get(id))?;

                tracing::debug!("storing result: {:?}", res_net);

                self.evaluations
                    .insert(self.reduction.as_ref()?.call_sig.clone(), res_net.clone());

                tracing::trace!("machine updated to: {:?}", self);
            }
            Op::PushInstr(op) => {
                self.reduction
                    .as_mut()?
                    .stack
                    .push_back(StackElem::Instr(*op));
            }
            Op::CondExec => {
                if let Some((cmp, (Some(exec_true), Some(exec_false)))) = self
                    .reduction
                    .as_mut()?
                    .stack
                    .pop_back()
                    .and_then(|maybe_cond| maybe_cond.as_bool().copied())
                    .zip(
                        self.reduction
                            .as_mut()?
                            .stack
                            .pop_back()
                            .map(|maybe_op_true| maybe_op_true.as_instr().cloned())
                            .zip(
                                self.reduction
                                    .as_mut()?
                                    .stack
                                    .pop_back()
                                    .map(|maybe_op_false| maybe_op_false.as_instr().cloned()),
                            ),
                    )
                {
                    self.reduction.as_mut()?.instructions.push_front(if cmp {
                        exec_true
                    } else {
                        exec_false
                    });

                    self.step_frame()?;
                }
            }
            Op::PushEq => {
                if let Some((cmp_a, cmp_b)) = self
                    .reduction
                    .as_mut()?
                    .stack
                    .pop_back()
                    .zip(self.reduction.as_mut()?.stack.pop_back())
                {
                    self.reduction
                        .as_mut()?
                        .stack
                        .push_back(StackElem::Bool(cmp_a == cmp_b));
                }
            }
            Op::PushNeq => {
                if let Some((cmp_a, cmp_b)) = self
                    .reduction
                    .as_mut()?
                    .stack
                    .pop_back()
                    .zip(self.reduction.as_mut()?.stack.pop_back())
                {
                    self.reduction
                        .as_mut()?
                        .stack
                        .push_back(StackElem::Bool(cmp_a != cmp_b));
                }
            }
            Op::PushNone => {
                if let Some(cmp_a) = self.reduction.as_mut()?.stack.pop_back() {
                    self.reduction
                        .as_mut()?
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
                let n_ptr =
                    if let Some(StackElem::Ptr(ptr)) = self.reduction.as_mut()?.stack.pop_back() {
                        ptr
                    } else {
                        return None;
                    };

                // Will need to add nodes, conns, or vars to this
                let net = self.reduction.as_mut()?.nets.get_mut(n_ptr)?;

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
                            ports: Default::default(),
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

                        net.active_pairs.push((a_ptr, b_ptr));
                    }
                    _ => {
                        unreachable!()
                    }
                }

                // We will need this for further operations, and for our outputresult
                self.reduction
                    .as_mut()?
                    .stack
                    .push_back(StackElem::Ptr(n_ptr));
            }
        }

        Some(())
    }

    //// TODO: Make this iterative
    pub fn readback_node(&self, buffer: &NetBuffer, node: &Node) -> Option<Port> {
        match node {
            Node::Agent { name, ports } => Some(Port::Agent(Agent {
                name: Type(self.p.names.get(*name)?.clone().0),
                ports: ports
                    .iter()
                    .filter_map(|p| self.readback_node(buffer, buffer.nodes.get(p.as_ptr())?))
                    .collect(),
            })),
            Node::Var { name, .. } => Some(Port::Var(Ident(self.p.names.get(*name)?.clone().0))),
        }
    }

    pub fn readback_buffer(&self, buffer: NetBuffer) -> Vec<(Option<Agent>, Option<Agent>)> {
        let deref_ptr_node = |p: Ptr| &buffer.nodes[p];

        buffer
            .active_pairs
            .iter()
            .map(|(a, b)| (deref_ptr_node(*a), deref_ptr_node(*b)))
            .map(|(a_node, b_node)| {
                (
                    self.readback_node(&buffer, a_node)
                        .and_then(|a| a.into_agent()),
                    self.readback_node(&buffer, b_node)
                        .and_then(|a| a.into_agent()),
                )
            })
            .collect::<Vec<(Option<Agent>, Option<Agent>)>>()
    }

    /// Converts the program to a human-readable form
    pub fn readback(&self) -> TypedProgram {
        TypedProgram {
            types: self
                .p
                .reductions
                .iter()
                .fold(Default::default(), |mut acc, ((lhs, rhs), _)| {
                    acc.insert(lhs.name.clone());
                    acc.insert(rhs.name.clone());

                    acc
                }),
            symbol_declarations_for: self.p.reductions.iter().fold(
                Default::default(),
                |mut acc, ((lhs, rhs), _)| {
                    if let Some((ty_lhs, ty_rhs)) = self
                        .p
                        .type_signature_for(lhs)
                        .zip(self.p.type_signature_for(rhs))
                    {
                        acc.insert(lhs.name.clone(), ty_lhs.ports.clone());
                        acc.insert(rhs.name.clone(), ty_rhs.ports.clone());
                    }

                    acc
                },
            ),
            nets: self
                .evaluations
                .iter()
                .map(|(_, buff)| {
                    self.readback_buffer(buff.clone())
                        .into_iter()
                        .map(|(lhs, rhs)| Net { lhs, rhs })
                        .collect::<Vec<_>>()
                })
                .flatten()
                .collect::<BTreeSet<_>>(),
        }
    }

    /// Steps the virtual machine until nothing in the stack is left to execute
    pub fn step_to_end(&mut self) {
        tracing::debug!("evaluating to end: \n{}", self.p);

        // We are done once we have no results
        // left to evaluate
        loop {
            if let Some(next) = self
                .p
                .active_pairs
                .clone()
                .iter()
                .filter_map(|(a, b)| Some((a.clone()?, b.clone()?)))
                .filter(|(a, b)| {
                    self.p.reductions.contains_key(&(a.clone(), b.clone()))
                        && !self.evaluations.contains_key(&(a.clone(), b.clone()))
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

        tracing::debug!("reducing redex {} >< {}", a, b);

        // Check if we have a rule to reduce the redex
        if let Some(reduction) = self.p.reductions.get(&(a.clone(), b.clone())) {
            tracing::debug!("found reduction for redex {} >< {}", a, b);

            // Attempt to execute the reduction for this active pair
            self.reduction = Some(ReductionFrame::new(
                reduction.into_iter().cloned().collect(),
                (a.clone(), b.clone()),
            ));

            tracing::trace!(
                "attempting to initiate step with frame {:?}",
                self.reduction
            );

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
