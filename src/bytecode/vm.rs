use super::{Op, Program, Ptr};
use crate::{
    heuristics::TypedProgram,
    parser::ast_lafont::{Agent, Ident, Net, Port, Type},
};
use std::collections::{linked_list::LinkedList, BTreeMap, BTreeSet, VecDeque};

#[derive(Clone, Debug, PartialEq)]
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
    Agent { name: Ptr, ports: Vec<Ptr> },

    /// Primary port is a pointer to the agent which the variable
    /// is connected to by output
    Var { name: Ptr, primary_port: Ptr },
}

impl Node {
    pub fn connect(self, other: Ptr) -> Self {
        match self {
            Self::Agent { name, mut ports } => {
                ports.push(other);

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

impl NetBuffer {
    pub fn connect(&mut self, a_ptr: Ptr, b_ptr: Ptr) {
        self.nodes[a_ptr] = self.nodes.remove(a_ptr).connect(b_ptr);
        self.nodes[b_ptr] = self.nodes.remove(b_ptr).connect(a_ptr);
    }
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

    fn push_ast_agent_net_buffer(&self, buffer: &mut NetBuffer, agent: &Agent) -> Option<Ptr> {
        let name_ptr = self
            .p
            .names
            .iter()
            .position(|name| name.0 == agent.name.0)?;

        buffer.nodes.push(Node::Agent {
            name: name_ptr,
            ports: Default::default(),
        });

        Some(buffer.nodes.len() - 1)
    }

    /// Todo: make this iterative
    pub fn new_net_buffer(&self, net: &Net) -> NetBuffer {
        let mut n = NetBuffer::default();

        // Push all agents in one pass
        // then connect them

        let mut to_insert_nodes = VecDeque::from_iter(
            [net.lhs.as_ref(), net.rhs.as_ref()]
                .into_iter()
                .filter_map(|x| x),
        );
        let mut inserted: BTreeMap<&Agent, Ptr> = Default::default();

        while let Some(to_insert) = to_insert_nodes.pop_front() {
            if inserted.contains_key(to_insert) {
                continue;
            }

            if let Some(agent_ptr) = self.push_ast_agent_net_buffer(&mut n, to_insert) {
                inserted.insert(to_insert, agent_ptr);
            }

            to_insert_nodes.extend(to_insert.ports.iter().filter_map(|p| match p {
                Port::Agent(a) => Some(a),
                Port::Var(_) => None,
            }));
        }

        // Now connect all inserted nodes
        let mut to_connect_nodes = VecDeque::from_iter(
            [net.lhs.as_ref(), net.rhs.as_ref()]
                .into_iter()
                .filter_map(|x| x),
        );

        while let Some((to_connect, to_connect_inserted)) = to_connect_nodes
            .pop_front()
            .and_then(|to_connect| Some((to_connect, inserted.get(to_connect)?)))
        {
            for port in to_connect.ports.iter() {
                match port {
                    Port::Agent(a) => {
                        let ptr_child = if let Some(v) = inserted.get(&a) {
                            v
                        } else {
                            continue;
                        };

                        n.connect(*to_connect_inserted, *ptr_child);

                        to_connect_nodes.extend(a.ports.iter().filter_map(|p| p.as_agent()));
                    }
                    Port::Var(v) => {
                        let name_ptr = if let Some(v) = self.p.names.iter().position(|x| x.0 == v.0)
                        {
                            v
                        } else {
                            continue;
                        };

                        n.nodes.push(Node::Var {
                            name: name_ptr,
                            primary_port: *to_connect_inserted,
                        });
                        let ptr = n.nodes.len() - 1;

                        n.connect(*to_connect_inserted, ptr);
                    }
                }
            }
        }

        n
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
            | p @ Op::PushConn(_, _)
            | p @ Op::PushPtrCpyNet(_) => {
                let n_ptr = if let Some(StackElem::Ptr(ptr)) =
                    self.reduction.as_ref()?.stack.iter().next().cloned()
                {
                    ptr
                } else {
                    return None;
                };

                match p {
                    Op::PushPtrCpyNet(n) => {
                        let (lhs, rhs) = self.p.active_pairs.get(n)?;
                        let buffer = self.new_net_buffer(&Net {
                            lhs: lhs.clone(),
                            rhs: rhs.clone(),
                        });

                        self.reduction.as_mut()?.nets.push(buffer);

                        let ptr = StackElem::Ptr(
                            self.reduction.as_ref()?.nets.get(n_ptr)?.nodes.len() - 1,
                        );

                        self.reduction.as_mut()?.stack.push_back(ptr);
                    }
                    Op::PushNodeVar(name_ptr, primary_port_ptr) => {
                        self.reduction
                            .as_mut()?
                            .nets
                            .get_mut(n_ptr)?
                            .nodes
                            .push(Node::Var {
                                name: name_ptr,
                                primary_port: primary_port_ptr,
                            });

                        // We will need this for further operations, and for our outputresult
                        let ptr = StackElem::Ptr(
                            self.reduction.as_ref()?.nets.get(n_ptr)?.nodes.len() - 1,
                        );

                        self.reduction.as_mut()?.stack.push_back(ptr);
                    }
                    Op::PushNodeAgent(name_ptr) => {
                        self.reduction
                            .as_mut()?
                            .nets
                            .get_mut(n_ptr)?
                            .nodes
                            .push(Node::Agent {
                                name: name_ptr,
                                ports: Default::default(),
                            });

                        // We will need this for further operations, and for our outputresult
                        let ptr = StackElem::Ptr(
                            self.reduction.as_ref()?.nets.get(n_ptr)?.nodes.len() - 1,
                        );

                        self.reduction.as_mut()?.stack.push_back(ptr);
                    }
                    Op::PushConn(a_ptr, b_ptr) => {
                        let net = self.reduction.as_mut()?.nets.get_mut(n_ptr)?;

                        net.connect(a_ptr, b_ptr);
                    }
                    _ => {
                        unreachable!()
                    }
                }
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
                    .filter_map(|p| self.readback_node(buffer, buffer.nodes.get(*p)?))
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
        tracing::trace!("evaluating to end: \n{}", self.p);

        // We are done once we have no results
        // left to evaluate
        while let Some(next) = self
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
