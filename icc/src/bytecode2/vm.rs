use super::{Agent, AgentPtr, GlobalPtr, Op, Ptr, StackElem};
use crate::parser::ast_lafont::{self as ast, Expr, Ident, Net, Port, PortKind, Type};
use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::{error, fmt};

#[derive(Copy, Clone, Debug)]
pub enum Error {
    /// There are no instructions left to advance the machine with.
    NothingToAdvance,

    /// The machine failed to advance
    CouldNotAdvance,

    /// Ptr to a location that does not exist
    InvalidPtr,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::NothingToAdvance => write!(f, "nothing to advance"),
            Self::CouldNotAdvance => write!(f, "failed to advance"),
            Self::InvalidPtr => write!(f, "ptr out of bounds"),
        }
    }
}

impl error::Error for Error {}

#[derive(Debug, Serialize, Deserialize)]
pub struct State {
    pub pos: Ptr,
    pub stack: Vec<StackElem>,
    pub types: BTreeMap<Type, Vec<PortKind>>,
}

impl State {
    pub fn iter_deref<'a>(&'a self, p: GlobalPtr) -> impl Iterator<Item = StackElem> + 'a {
        DerefVisitor::new(self, p)
    }

    pub fn iter_ports(&self, p: GlobalPtr) -> Option<impl Iterator<Item = (AgentPtr, GlobalPtr)>> {
        let stack_pos = p.as_stack_ptr()?;
        let maybe_agent = self.iter_deref(p).last()?;
        let agent = maybe_agent.as_agent()?;

        Some(
            agent
                .ports
                .iter()
                .enumerate()
                .map(move |(port, port_value)| (AgentPtr { stack_pos, port }, port_value.clone()))
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
}

impl State {
    pub fn readback(&self, p: GlobalPtr) -> Option<Expr> {
        let pointers = self.iter_tree(p)?.collect::<Vec<_>>();

        let typed_agents = pointers
            .iter()
            .map(|ptr| {
                let elem = self.iter_deref(*ptr).last()?;
                let name = self.iter_deref(elem.as_agent()?.name).last()?;

                Some((
                    ptr.as_stack_ptr()?,
                    self.types.get(&Type(name.as_ident()?.to_owned()))?.clone(),
                ))
            })
            .collect::<Option<BTreeMap<Ptr, Vec<PortKind>>>>()?;
        let mut converted_agents: BTreeMap<Ptr, ast::Agent> = Default::default();

        // Find first redex
        let ((lhs_elem, lhs_ptr), (rhs_elem, rhs_ptr)): ((Agent, Ptr), (Agent, Ptr)) = pointers
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
                let (a_raw_ptr, b_raw_ptr) = (a.as_stack_ptr()?, b.as_stack_ptr()?);
                let (port_b, port_a) = (
                    a_elem.ports.iter().position(|elem| *elem == *a)?,
                    b_elem.ports.iter().position(|elem| *elem == *b)?,
                );
                let (a_ty, b_ty) = (typed_agents.get(&a_raw_ptr)?, typed_agents.get(&b_raw_ptr)?);

                if port_b != 0 && port_a != 0 {
                    return None;
                }

                // First ports must be opposite, and indices of ports must be first
                if !a_ty.get(port_b)?.is_complement(b_ty.get(port_a)?) {
                    return None;
                }

                Some(((a_elem.clone(), a_raw_ptr), (b_elem.clone(), b_raw_ptr)))
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

        // Assume that ports are in the same order in buffer representation
        // as in expression representation, except for redexes
        let mut to_insert: VecDeque<(Ptr, GlobalPtr)> = VecDeque::from_iter(
            lhs_elem
                .ports
                .iter()
                .map(|p| (lhs_ptr, *p))
                .chain(rhs_elem.ports.iter().map(|p| (rhs_ptr, *p))),
        );

        // Insert the redex members themselves as "roots:"
        // - they have no parents
        converted_agents.insert(lhs_ptr, ast::Agent::new(lhs_name));
        converted_agents.insert(rhs_ptr, ast::Agent::new(rhs_name));

        // Insert each child in the next available
        // port in its parent
        //
        // Its parent expression can be found in the converted_agents map
        // Vars do not have children, so they do not need to be looked up
        while let Some((parent_ptr, ins)) = to_insert.pop_front() {
            let elem = self.iter_deref(ins).last()?;

            let build: Port = match elem {
                StackElem::Var(v) => {
                    let name = self
                        .iter_deref(GlobalPtr::StackPtr(v))
                        .last()?
                        .as_ident()?
                        .to_owned();

                    Some(Port::Var(Ident(name)))
                }
                StackElem::Agent(a) => {
                    let name = self.iter_deref(a.name).last()?.as_ident()?.to_owned();

                    to_insert.extend(
                        a.ports
                            .iter()
                            .copied()
                            .map(|ptr| Some((ins.as_stack_ptr()?, ptr)))
                            .collect::<Option<Vec<_>>>()?,
                    );

                    Some(Port::Agent(ast::Agent {
                        name: Type(name),
                        ports: Default::default(),
                    }))
                }
                _ => None,
            }?;

            let parent = converted_agents.get_mut(&parent_ptr)?;
            parent.ports.push(build);
        }

        Some(Expr::Net(Net {
            lhs: Some(converted_agents.remove(&lhs_ptr)?),
            rhs: Some(converted_agents.remove(&rhs_ptr)?),
        }))
    }

    pub fn step(&mut self) -> Result<Option<Expr>, Error> {
        let next_elem = self.stack.get(self.pos).ok_or(Error::NothingToAdvance)?;

        let res = match next_elem {
            StackElem::Ident(_)
            | StackElem::Agent { .. }
            | StackElem::Ptr(_)
            | StackElem::Var(_) => Err(Error::CouldNotAdvance),
            StackElem::Instr(op) => match op.as_ref() {
                &Op::PushRes(p) => Ok(self.readback(p)),
                &Op::PushStackElem(ref e) => {
                    self.stack.push(e.clone());

                    Ok(None)
                }
            },
        };

        self.pos += 1;

        res
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
                GlobalPtr::StackPtr(p) => self.view.stack.get(p).cloned(),
                GlobalPtr::AgentPtr(AgentPtr { stack_pos, port }) => {
                    let elem = self.view.stack.get(stack_pos)?;

                    match elem {
                        StackElem::Agent(a) => {
                            let p = a.ports.get(port)?;

                            Some(StackElem::Ptr(*p))
                        }
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
