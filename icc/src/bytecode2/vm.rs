use super::{Agent, AgentPtr, GlobalPtr, Op, Program, Ptr, StackElem};
use crate::parser::ast_lafont::{self as ast, Expr, Ident, Net, Port, PortKind, Type};
use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::{error, fmt};

#[derive(Clone, Debug)]
pub enum Error {
    /// There are no instructions left to advance the machine with.
    NothingToAdvance,

    /// The machine failed to advance
    CouldNotAdvance { op: Op, args: Vec<StackElem> },

    /// Ptr to a location that does not exist
    InvalidPtr,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::NothingToAdvance => write!(f, "nothing to advance"),
            Self::CouldNotAdvance { op, args } => write!(
                f,
                "failed to advance with next step {} and args {:?}",
                op, args
            ),
            Self::InvalidPtr => write!(f, "ptr out of bounds"),
        }
    }
}

impl error::Error for Error {}

#[derive(Debug, Serialize, Deserialize)]
pub struct State {
    pub pos: Ptr,
    pub src: Program,
    pub stack: VecDeque<StackElem>,
    pub mem: Vec<StackElem>,
    pub types: BTreeMap<Type, Vec<PortKind>>,
    pub redex_bag: VecDeque<(GlobalPtr, GlobalPtr)>,
}

impl State {
    pub fn new(program: Program, types: BTreeMap<Type, Vec<PortKind>>) -> Self {
        Self {
            pos: Default::default(),
            src: program,
            mem: Default::default(),
            stack: Default::default(),
            redex_bag: Default::default(),
            types,
        }
    }

    pub fn iter_deref<'a>(&'a self, p: GlobalPtr) -> impl Iterator<Item = StackElem> + 'a {
        DerefVisitor::new(self, p)
    }

    pub fn iter_ports(&self, p: GlobalPtr) -> Option<impl Iterator<Item = (AgentPtr, GlobalPtr)>> {
        let mem_pos = p.as_mem_ptr()?;
        let maybe_agent = self.iter_deref(p).last()?;
        let agent = maybe_agent.as_agent()?;

        Some(
            agent
                .ports
                .iter()
                .enumerate()
                .map(move |(port, port_value)| {
                    (
                        AgentPtr {
                            mem_pos,
                            port: Some(port),
                        },
                        port_value.clone(),
                    )
                })
                .collect::<Vec<_>>()
                .into_iter(),
        )
    }

    pub fn iter_port_values(
        &self,
        stack_ptr: GlobalPtr,
    ) -> Option<impl Iterator<Item = GlobalPtr>> {
        Some(self.iter_ports(stack_ptr)?.map(|(_, x)| x))
    }

    pub fn iter_tree<'a>(
        &'a self,
        stack_ptr: GlobalPtr,
    ) -> Option<impl Iterator<Item = GlobalPtr> + 'a> {
        Some(TreeVisitor::new(self, stack_ptr))
    }

    pub fn readback(&self, p: GlobalPtr) -> Option<Expr> {
        let pointers = self.iter_tree(p)?.collect::<Vec<_>>();

        let typed_agents = pointers
            .iter()
            .map(|ptr| {
                let elem = self.iter_deref(*ptr).last()?;
                let name = self.iter_deref(elem.as_agent()?.name).last()?;

                Some((
                    ptr.as_mem_ptr()?,
                    self.types.get(&Type(name.as_ident()?.to_owned()))?.clone(),
                ))
            })
            .collect::<Option<BTreeMap<Ptr, Vec<PortKind>>>>()?;

        // Find first redex
        let (lhs_elem, rhs_elem): (Agent, Agent) = pointers
            .iter()
            .map(|x| {
                pointers
                    .iter()
                    .filter(move |y| x != *y)
                    .map(move |y| (x, y))
            })
            .flatten()
            .filter_map(|(a, b)| {
                let (a_elem, b_elem) = (
                    self.iter_deref(*a)
                        .last()
                        .and_then(|x| Some(x.as_agent()?.clone()))?,
                    self.iter_deref(*b)
                        .last()
                        .and_then(|x| Some(x.as_agent()?.clone()))?,
                );
                let (a_raw_ptr, b_raw_ptr) = (a.as_mem_ptr()?, b.as_mem_ptr()?);

                let (port_b, port_a) = (
                    a_elem.ports.iter().position(|elem| *elem == *b)?,
                    b_elem.ports.iter().position(|elem| *elem == *a)?,
                );
                let (a_ty, b_ty) = (typed_agents.get(&a_raw_ptr)?, typed_agents.get(&b_raw_ptr)?);

                if port_b != 0 && port_a != 0 {
                    return None;
                }

                // First ports must be opposite, and indices of ports must be first
                if !a_ty.get(port_b)?.is_complement(b_ty.get(port_a)?) {
                    return None;
                }

                Some((a_elem.clone(), b_elem.clone()))
            })
            .next()?;

        let (lhs_name, rhs_name) = (
            self.iter_deref(lhs_elem.name)
                .last()
                .and_then(|elem| Some(elem.as_ident()?.to_owned()))?,
            self.iter_deref(rhs_elem.name)
                .last()
                .and_then(|elem| Some(elem.as_ident()?.to_owned()))?,
        );

        let (mut lhs_agent, mut rhs_agent) = (ast::Agent::new(lhs_name), ast::Agent::new(rhs_name));
        lhs_agent.ports = lhs_elem
            .ports
            .iter()
            .skip(1)
            .filter_map(|p| self.readback_elem(*p, &mut Default::default()))
            .collect();
        rhs_agent.ports = rhs_elem
            .ports
            .iter()
            .skip(1)
            .filter_map(|p| self.readback_elem(*p, &mut Default::default()))
            .collect();

        Some(Expr::Net(Net {
            lhs: Some(lhs_agent),
            rhs: Some(rhs_agent),
        }))
    }

    pub fn readback_elem(&self, p: GlobalPtr, seen: &mut BTreeSet<GlobalPtr>) -> Option<Port> {
        if seen.contains(&p) {
            return None;
        }

        seen.insert(p);

        let elem = self.iter_deref(p).last()?;

        let build: Port = match elem {
            StackElem::Var(v) => {
                let name = self
                    .iter_deref(GlobalPtr::MemPtr(v))
                    .last()?
                    .as_ident()?
                    .to_owned();

                Some(Port::Var(Ident(name)))
            }
            StackElem::Agent(a) => {
                let name = self.iter_deref(a.name).last()?.as_ident()?.to_owned();

                Some(Port::Agent(ast::Agent {
                    name: Type(name),
                    ports: a
                        .ports
                        .iter()
                        .skip(1)
                        .filter_map(|p| self.readback_elem(*p, seen))
                        .collect::<Vec<_>>(),
                }))
            }
            _ => None,
        }?;

        Some(build)
    }

    pub fn step(&mut self) -> Result<Option<Expr>, Error> {
        let next_elem = if let StackElem::Instr(o) = self
            .src
            .get(self.pos)
            .cloned()
            .ok_or(Error::NothingToAdvance)?
        {
            o
        } else {
            self.pos += 1;

            return Ok(None);
        };

        let stack_snapshot = self.stack.clone();

        tracing::trace!(
            "attempting op execution {} with args {:?} at line {}",
            next_elem,
            stack_snapshot,
            self.pos,
        );

        let res = (|| -> Option<Option<Expr>> {
            let res = match next_elem.as_ref() {
                &Op::Connect => {
                    let (ptr_a, ptr_b) = (
                        self.stack.pop_back()?.into_ptr()?.into_agent_ptr()?,
                        self.stack.pop_back()?.into_ptr()?.into_agent_ptr()?,
                    );

                    let agent_a = self.src.0.get_mut(ptr_a.mem_pos)?.as_agent_mut()?;
                    agent_a
                        .ports
                        .insert(ptr_a.port.unwrap_or_default(), GlobalPtr::AgentPtr(ptr_b));

                    let agent_b = self.src.0.get_mut(ptr_b.mem_pos)?.as_agent_mut()?;
                    agent_b
                        .ports
                        .insert(ptr_b.port.unwrap_or_default(), GlobalPtr::AgentPtr(ptr_a));

                    Some(None)
                }
                &Op::PopRedex => {
                    let redex = self.redex_bag.pop_back()?;

                    self.stack.push_back(StackElem::Ptr(redex.0));
                    self.stack.push_back(StackElem::Ptr(redex.1));

                    Some(None)
                }
                &Op::RefIndex => {
                    let offset = self
                        .stack
                        .pop_back()
                        .and_then(|elem| elem.into_ptr()?.into_mem_ptr())?;

                    let ptr = self.stack.pop_back()?.into_ptr()?.into_mem_ptr()?;

                    self.stack
                        .push_back(StackElem::Ptr(GlobalPtr::AgentPtr(AgentPtr {
                            mem_pos: ptr,
                            port: Some(offset),
                        })));

                    Some(None)
                }
                &Op::PortPtr => {
                    let port = self.stack.pop_back()?.into_ptr()?.into_agent_ptr()?;
                    self.stack
                        .push_back(StackElem::Ptr(GlobalPtr::MemPtr(port.mem_pos)));

                    Some(None)
                }
                &Op::Copy => {
                    let to_cpy = self.stack.pop_back()?;

                    self.stack.push_back(to_cpy.clone());
                    self.stack.push_back(to_cpy);

                    Some(None)
                }
                &Op::PushStack(ref elem) => {
                    self.stack.push_back(elem.clone());

                    Some(None)
                }
                &Op::Load => {
                    let elem = self.stack.pop_back()?;
                    let ptr = elem.as_ptr()?;
                    let loaded = self.iter_deref(*ptr).last()?;

                    self.stack.push_back(loaded);

                    Some(None)
                }
                &Op::LoadMem => {
                    let elem = self.stack.pop_back()?;
                    let ptr = elem.as_ptr()?;

                    if let Some(loaded) = self.mem.get(ptr.as_mem_ptr()?) {
                        self.stack.push_back(loaded.clone());
                    } else {
                        self.stack.push_back(StackElem::None);
                    }

                    Some(None)
                }
                &Op::StoreAt => {
                    let pos = self
                        .stack
                        .pop_back()
                        .as_ref()
                        .and_then(|elem| elem.as_ptr()?.as_mem_ptr())?;
                    let to_store = self.stack.pop_back()?;

                    if pos < self.mem.len() {
                        *self.mem.get_mut(pos)? = to_store;
                    } else {
                        self.mem.push(to_store);
                    }

                    Some(None)
                }
                &Op::PushRes => {
                    let to_push = self
                        .stack
                        .pop_back()
                        .and_then(|elem| elem.as_ptr().cloned())?;

                    Some(Some(self.readback(to_push)?))
                }
                &Op::Debug => {
                    let p = self.stack.pop_back()?;

                    tracing::debug!("{}", p);

                    Some(None)
                }
                &Op::DebugMem => {
                    tracing::debug!("{:?}", self.mem);

                    Some(None)
                }
                &Op::Cmp => {
                    let (deref_a, deref_b) = (self.stack.pop_back(), self.stack.pop_back());

                    self.stack.push_back(StackElem::Bool(deref_a == deref_b));

                    Some(None)
                }
                &Op::GoTo => {
                    let pos = self
                        .stack
                        .pop_back()
                        .and_then(|elem| elem.as_ptr()?.as_mem_ptr())?;
                    self.pos = pos;

                    return Some(None);
                }
                Op::GoToEq => {
                    let pos = self.stack.pop_back()?.as_ptr()?.as_mem_ptr()?;
                    let a = self.stack.pop_back()?;
                    let b = self.stack.pop_back()?;

                    if a != b {
                        self.pos += 1;

                        return Some(None);
                    }

                    self.pos = pos;

                    return Some(None);
                }
                Op::GoToNeq => {
                    let pos = self.stack.pop_back()?.as_ptr()?.as_mem_ptr()?;
                    let a = self.stack.pop_back()?;
                    let b = self.stack.pop_back()?;

                    if a == b {
                        self.pos += 1;

                        return Some(None);
                    }

                    self.pos = pos;

                    return Some(None);
                }
                &Op::CondExec => {
                    let recent_ops = [
                        self.stack.pop_back()?,
                        self.stack.pop_back()?,
                        self.stack.pop_back()?,
                    ];

                    match &recent_ops[..] {
                        &[StackElem::Instr(ref a), StackElem::Instr(_), StackElem::Bool(true)]
                        | &[StackElem::Instr(_), StackElem::Instr(ref a), StackElem::Bool(false)] =>
                        {
                            self.stack.push_back(StackElem::Instr(a.clone()));

                            Some(None)
                        }
                        _ => None,
                    }
                }
                &Op::Deref => {
                    let recent_ptr = self.stack.pop_back().and_then(|elem| elem.into_ptr())?;

                    let deref = self
                        .iter_deref(recent_ptr)
                        .filter(|elem| elem.as_ptr() != Some(&recent_ptr))
                        .next();

                    self.stack.push_back(deref.unwrap_or(StackElem::None));

                    Some(None)
                }
                &Op::IncrPtr => {
                    let offset = self.stack.pop_back().and_then(|elem| elem.into_offset())?;
                    let recent_ptr = self.stack.pop_back().and_then(|elem| elem.into_ptr())?;
                    self.stack
                        .push_back(StackElem::Ptr(recent_ptr.add_offset(offset)?));

                    Some(None)
                }
            };

            self.pos += 1;

            res
        })()
        .ok_or(Error::CouldNotAdvance {
            op: *next_elem,
            args: stack_snapshot.clone().into(),
        });

        res
    }

    pub fn step_to_end(&mut self) -> Result<Vec<Expr>, Error> {
        let mut results = Vec::default();

        while self.pos < self.src.len() {
            if let Some(res) = self.step()? {
                results.push(res);
            }
        }

        Ok(results)
    }
}

#[derive(Debug)]
pub struct DerefVisitor<'a> {
    pos: Option<GlobalPtr>,
    view: &'a State,
}

impl<'a> DerefVisitor<'a> {
    pub fn new(view: &'a State, pos: GlobalPtr) -> Self {
        Self {
            pos: Some(pos),
            view,
        }
    }
}

impl Iterator for DerefVisitor<'_> {
    type Item = StackElem;

    fn next(&mut self) -> Option<Self::Item> {
        let curr = {
            match self.pos? {
                GlobalPtr::MemPtr(p) => self.view.src.get(p).cloned(),
                GlobalPtr::Offset(_) => unimplemented!(),
                GlobalPtr::AgentPtr(AgentPtr { mem_pos, port }) => {
                    let elem = self.view.src.get(mem_pos)?;

                    match (elem, port) {
                        (StackElem::Agent(a), Some(port)) => {
                            let p = a.ports.get(port)?;

                            Some(StackElem::Ptr(*p))
                        }
                        (StackElem::Agent(a), _) => Some(StackElem::Agent(a.clone())),
                        _ => None,
                    }
                    .clone()
                }
            }
        }?;

        match curr {
            StackElem::Ptr(p) => {
                self.pos = Some(p);
            }
            _ => {
                self.pos = None;
            }
        }

        Some(curr.clone())
    }
}

#[derive(Debug)]
pub struct TreeVisitor<'a> {
    seen: BTreeSet<GlobalPtr>,
    to_visit: VecDeque<GlobalPtr>,
    view: &'a State,
}

impl<'a> TreeVisitor<'a> {
    pub fn new(view: &'a State, pos: GlobalPtr) -> Self {
        Self {
            to_visit: VecDeque::from_iter([pos]),
            seen: Default::default(),
            view,
        }
    }
}

impl Iterator for TreeVisitor<'_> {
    type Item = GlobalPtr;

    fn next(&mut self) -> Option<Self::Item> {
        let curr_ptr = self
            .to_visit
            .iter()
            .skip_while(|x| self.seen.contains(x))
            .next()
            .copied()?;

        self.seen.insert(curr_ptr);

        self.to_visit.extend(
            self.view
                .iter_ports(curr_ptr)
                .map(|x| x.map(|(_, x)| x).collect::<Vec<_>>())
                .unwrap_or_default(),
        );

        Some(curr_ptr)
    }
}
