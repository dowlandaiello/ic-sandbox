use super::{Op, Program, Ptr};
use crate::{
    heuristics::TypedProgram,
    parser::ast_lafont::{Agent, Ident, Net, Port, PortKind, Type},
};
use std::collections::{linked_list::LinkedList, BTreeMap, BTreeSet};

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

#[derive(Debug)]
pub struct ReductionFrame {
    pub stack: LinkedList<StackElem>,
    pub instructions: LinkedList<Op>,
    pub nets: Vec<Net>,
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
    pub evaluations: BTreeMap<(Agent, Agent), Net>,

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

    fn try_amortize_dyn<'a>(&self, n: Net) -> Net {
        fn amortize_from<'a>(
            typings: &'a BTreeMap<Type, Vec<PortKind>>,
            output_agent: &'a Agent,
        ) -> Option<Agent> {
            let type_dec = if let Some(typing) = typings.get(&output_agent.name) {
                typing.iter().cloned().skip(1).collect::<Vec<_>>()
            } else {
                return Default::default();
            };

            let terminal_ports = TypedProgram::terminal_ports_for(output_agent, &type_dec);

            tracing::debug!(
                "agent {} has terminal ports {}",
                output_agent,
                terminal_ports
                    .iter()
                    .map(|s| s.to_string())
                    .collect::<Vec<_>>()
                    .join(", "),
            );

            terminal_ports
                .into_iter()
                .filter_map(|p| match p {
                    // TODO: Use references for this
                    Port::Agent(a) => Some(a.clone()),
                    Port::Var(_) => None,
                })
                .next()
        }

        let lhs_out = n
            .lhs
            .and_then(|lhs| amortize_from(&self.p.symbol_declarations_for, &lhs));
        let rhs_out = n
            .rhs
            .and_then(|rhs| amortize_from(&self.p.symbol_declarations_for, &rhs));

        Net {
            lhs: lhs_out,
            rhs: rhs_out,
        }
    }

    pub fn step_frame(&mut self) -> Option<()> {
        let op = self.reduction.as_mut()?.instructions.pop_front()?;

        tracing::debug!("executing op {}", op);
        tracing::trace!("stack at execution: {:?}", self.reduction.as_ref()?.stack);

        match op {
            Op::Amortize => {
                let res_net_ptr = self
                    .reduction
                    .as_mut()?
                    .stack
                    .pop_back()
                    .and_then(|elem| elem.into_ptr())?;

                let res_net = self.reduction.as_mut()?.nets.remove(res_net_ptr);
                let new_net = self.try_amortize_dyn(res_net);

                self.reduction.as_mut()?.nets.insert(res_net_ptr, new_net);

                let ptr = StackElem::Ptr(res_net_ptr);
                self.reduction.as_mut()?.stack.push_back(ptr);
            }
            Op::Rename(name_ptr, val) => {
                tracing::trace!("renaming {} to {}", name_ptr, val);

                let res_net_ptr = self
                    .reduction
                    .as_mut()?
                    .stack
                    .pop_back()
                    .and_then(|elem| elem.into_ptr())?;

                let res_net = self.reduction.as_mut()?.nets.get_mut(res_net_ptr)?;

                let name_deref = self.p.names.get(name_ptr)?;

                res_net.replace_name(Ident(name_deref.0.clone()), val);

                tracing::trace!("renamed: {}", res_net);

                let ptr = StackElem::Ptr(res_net_ptr);
                self.reduction.as_mut()?.stack.push_back(ptr);
            }
            Op::CutAgent(agent) => {
                tracing::trace!("copying {} to buffer", agent);

                let buffer = Net {
                    lhs: Some(agent.clone()),
                    rhs: None,
                };

                self.reduction.as_mut()?.nets.push(buffer);

                let ptr = StackElem::Ptr(self.reduction.as_ref()?.nets.len() - 1);

                self.reduction.as_mut()?.stack.push_back(ptr);
            }
            Op::PushPtrInitNet => {
                self.reduction.as_mut()?.nets.push(Net {
                    lhs: None,
                    rhs: None,
                });
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

            Op::PushPtrCpyNet(n) => {
                tracing::trace!("copying {} to buffer", n);

                let (lhs, rhs) = self.p.active_pairs.get(n)?;

                tracing::trace!(
                    "copying {} >< {} to buffer",
                    lhs.as_ref().map(|a| a.to_string()).unwrap_or_default(),
                    rhs.as_ref().map(|a| a.to_string()).unwrap_or_default(),
                );

                let buffer = Net {
                    lhs: lhs.clone(),
                    rhs: rhs.clone(),
                };

                tracing::trace!(
                    "copied {} >< {} to buffer {}",
                    lhs.as_ref().map(|a| a.to_string()).unwrap_or_default(),
                    rhs.as_ref().map(|a| a.to_string()).unwrap_or_default(),
                    buffer
                );

                self.reduction.as_mut()?.nets.push(buffer);

                let ptr = StackElem::Ptr(self.reduction.as_ref()?.nets.len() - 1);

                self.reduction.as_mut()?.stack.push_back(ptr);
            }
        }

        Some(())
    }

    /// Converts the program to a human-readable form
    pub fn readback(&self) -> TypedProgram {
        let types =
            self.p
                .reductions
                .iter()
                .fold(BTreeSet::default(), |mut acc, ((lhs, rhs), _)| {
                    acc.insert(lhs.name.clone());
                    acc.insert(rhs.name.clone());

                    acc
                });

        let symbol_declarations_for =
            self.p
                .reductions
                .iter()
                .fold(BTreeMap::default(), |mut acc, ((lhs, rhs), _)| {
                    if let Some((ty_lhs, ty_rhs)) = self
                        .p
                        .type_signature_for(lhs)
                        .zip(self.p.type_signature_for(rhs))
                    {
                        acc.insert(lhs.name.clone(), ty_lhs.ports.clone());
                        acc.insert(rhs.name.clone(), ty_rhs.ports.clone());
                    }

                    acc
                });

        let nets = self
            .evaluations
            .iter()
            .map(|(_, buff)| buff)
            .cloned()
            .collect::<BTreeSet<_>>();

        TypedProgram {
            types,
            symbol_declarations_for,
            nets,
        }
    }

    /// Steps the virtual machine until nothing in the stack is left to execute
    pub fn step_to_end(&mut self) {
        tracing::trace!("evaluating to end: \n{}", self.p);

        // We are done once we have no results
        // left to evaluate
        loop {
            if let Some(next) = self
                .p
                .active_pairs
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

        tracing::trace!("done evaluating");
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
