use super::{Agent, AgentPtr, GlobalPtr, Op, Program, Ptr, StackElem};
use crate::parser::ast_lafont::{self as ast, Expr, Ident, Net, Port, PortKind, Type};
use serde::{Deserialize, Serialize};
use std::{
    collections::{BTreeMap, BTreeSet, VecDeque},
    error, fmt,
    rc::Rc,
};

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

#[derive(PartialEq, Clone, Debug)]
pub struct Substitution {
    src: GlobalPtr,
    dest: GlobalPtr,
}

#[derive(Serialize, Deserialize)]
pub struct State {
    pub pos: Ptr,
    pub src: Program,
    pub stack: VecDeque<StackElem>,
    pub mem: Vec<StackElem>,
    pub types: BTreeMap<Type, Vec<PortKind>>,
    pub redex_bag: VecDeque<(Ptr, Ptr)>,

    #[serde(skip)]
    pub results: BTreeMap<Rc<Vec<(RedexElem, RedexElem)>>, Expr>,

    #[serde(skip)]
    pub results_ord: Vec<Rc<Vec<(RedexElem, RedexElem)>>>,
}

#[derive(Debug, Ord, PartialOrd, PartialEq, Eq, Serialize, Deserialize)]
pub enum RedexElem {
    Agent { name: String },
    Var { name: String },
}

impl State {
    pub fn new(program: Program, types: BTreeMap<Type, Vec<PortKind>>) -> Self {
        let mut s = Self {
            pos: Default::default(),
            src: program,
            mem: Default::default(),
            stack: Default::default(),
            redex_bag: Default::default(),
            types,
            results: Default::default(),
            results_ord: Default::default(),
        };

        s.refresh_redex_bag();

        s
    }

    pub fn refresh_redex_bag(&mut self) {
        self.redex_bag = self
            .iter_redex_dyn()
            .map(|((a_pos, _), (b_pos, _))| (a_pos, b_pos))
            .collect();
    }

    pub fn iter_redex_dyn(&self) -> impl Iterator<Item = ((Ptr, &Agent), (Ptr, &Agent))> {
        let agents = self
            .src
            .0
            .iter()
            .skip(self.src.len())
            .enumerate()
            .filter_map(|(i, elem)| Some((i, elem.as_agent()?)));
        agents.filter_map(|(mem_pos, agent)| {
            let a = agent;
            let b_port_ptr = agent.ports.get(0)?.as_agent_ptr()?;
            let b = self.src.get(b_port_ptr.mem_pos)?.as_agent()?;

            if b_port_ptr.port != Some(0) {
                return None;
            }

            Some(((mem_pos, a), (b_port_ptr.mem_pos, b)))
        })
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

    pub fn subset_tree_positions(
        &self,
        ptr_child: Ptr,
        ptr_parent: Ptr,
    ) -> Option<Vec<Substitution>> {
        let filter_ptr_relevant = |ptr| {
            // We want vars and agents, not variables
            let elem = self
                .iter_deref(ptr)
                .filter(|elem| {
                    matches!(elem, StackElem::Agent(_)) || matches!(elem, StackElem::Var(_))
                })
                .next()?;

            Some((ptr, elem))
        };

        let mut iter_child = self
            .iter_tree(GlobalPtr::MemPtr(ptr_child))?
            .filter_map(filter_ptr_relevant)
            .collect::<VecDeque<_>>();
        let mut positions = Vec::new();

        let parent_tree = self
            .iter_tree(GlobalPtr::MemPtr(ptr_parent))?
            .collect::<Vec<_>>();

        for (ptr, node) in parent_tree.into_iter().filter_map(filter_ptr_relevant) {
            let (corresponding, corresponding_elem) = iter_child.pop_front()?;

            match node {
                StackElem::Agent(a) => match corresponding_elem {
                    StackElem::Var(_) => {
                        return None;
                    }
                    StackElem::Agent(b) => {
                        let a_name = self.iter_deref(a.name).last();
                        let b_name = self.iter_deref(a.name).last();

                        if a_name == b_name && a.ports.len() == b.ports.len() {
                            continue;
                        }
                    }
                    _ => {
                        return None;
                    }
                },
                // Advance the corresponding pointers to the next non-child pointer
                StackElem::Var(_) => {
                    positions.push(Substitution {
                        src: ptr,
                        dest: corresponding,
                    });

                    // Skip all child pointers
                    let mut subtree = self.iter_tree(corresponding)?;
                    iter_child = iter_child
                        .into_iter()
                        .skip_while(|(ptr, _)| subtree.next() == Some(*ptr))
                        .collect();

                    continue;
                }
                _ => {
                    return None;
                }
            }
        }

        Some(positions)
    }

    pub fn clone_tree(&mut self, p: Ptr) -> Option<Ptr> {
        let all_elems = self.iter_tree(GlobalPtr::MemPtr(p))?.collect::<Vec<_>>();
        let mut new_elems = all_elems
            .into_iter()
            .filter_map(|ptr| {
                // We want vars and agents, not variables
                let elem = self
                    .iter_deref(ptr)
                    .filter(|elem| {
                        matches!(elem, StackElem::Agent(_)) || matches!(elem, StackElem::Var(_))
                    })
                    .next()?;

                match elem {
                    StackElem::Agent(a) => {
                        let name = {
                            let name = self.src.get(a.name.as_mem_ptr()?)?.clone();
                            self.src.0.push(name);

                            Some(self.src.len() - 1)
                        }?;

                        self.src.0.push(StackElem::Agent(Agent {
                            name: GlobalPtr::MemPtr(name),
                            ports: Default::default(),
                        }));

                        Some((ptr, self.src.len() - 1))
                    }
                    StackElem::Var(v) => {
                        let name = {
                            let name = self.src.get(v)?.clone();
                            self.src.0.push(name);

                            Some(self.src.len() - 1)
                        }?;

                        self.src.0.push(StackElem::Var(name));

                        Some((ptr, self.src.len() - 1))
                    }
                    _ => None,
                }
            })
            .collect::<BTreeMap<GlobalPtr, Ptr>>();

        // Now connect elems as they were in the original
        let _ = new_elems
            .iter()
            .filter_map(|(original, new)| Some((original.as_mem_ptr()?, new)))
            .filter_map(|(original, new)| {
                let new_ports = self
                    .src
                    .get(original)?
                    .as_agent()?
                    .ports
                    .iter()
                    .map(|p| match p {
                        GlobalPtr::AgentPtr(p) => Some(GlobalPtr::AgentPtr(AgentPtr {
                            mem_pos: *new_elems.get(&GlobalPtr::MemPtr(p.mem_pos))?,
                            port: p.port,
                        })),
                        GlobalPtr::MemPtr(p) => {
                            Some(GlobalPtr::MemPtr(*new_elems.get(&GlobalPtr::MemPtr(*p))?))
                        }
                        _ => None,
                    })
                    .collect::<Option<Vec<_>>>()?;
                let new_mut = self.src.0.get_mut(*new)?.as_agent_mut()?;

                new_mut.ports = new_ports;

                Some(())
            })
            .collect::<Vec<_>>();

        new_elems.remove(&GlobalPtr::MemPtr(p))
    }

    pub fn iter_tree<'a>(
        &'a self,
        stack_ptr: GlobalPtr,
    ) -> Option<impl Iterator<Item = GlobalPtr> + 'a> {
        Some(TreeVisitor::new(self, stack_ptr))
    }

    pub fn readback(&self, p: GlobalPtr) -> Option<Expr> {
        let pointers = self
            .iter_tree(p)?
            .filter(|ptr| ptr.as_mem_ptr().is_some())
            .collect::<Vec<_>>();

        let typed_agents = pointers
            .iter()
            .filter_map(|ptr| {
                let elem = self
                    .iter_deref(*ptr)
                    .filter_map(|elem| elem.into_agent())
                    .next()?;
                let name = self.iter_deref(elem.name).last()?;

                Some((
                    ptr.as_mem_ptr()?,
                    self.types.get(&Type(name.as_ident()?.to_owned()))?.clone(),
                ))
            })
            .collect::<BTreeMap<Ptr, Vec<PortKind>>>();

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
                        .filter_map(|elem| elem.into_agent())
                        .next()?,
                    self.iter_deref(*b)
                        .filter_map(|elem| elem.into_agent())
                        .next()?,
                );
                let (a_raw_ptr, b_raw_ptr) = (a.as_mem_ptr()?, b.as_mem_ptr()?);

                let (port_b, port_a) = (
                    a_elem.ports.iter().position(|elem| {
                        (|| Some(elem.as_agent_ptr()?.mem_pos == b_raw_ptr))().unwrap_or_default()
                    })?,
                    b_elem.ports.iter().position(|elem| {
                        (|| Some(elem.as_agent_ptr()?.mem_pos == a_raw_ptr))().unwrap_or_default()
                    })?,
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
            .filter_map(|p| self.readback_elem(p.get_src_pos()?, &mut Default::default()))
            .collect();
        rhs_agent.ports = rhs_elem
            .ports
            .iter()
            .skip(1)
            .filter_map(|p| self.readback_elem(p.get_src_pos()?, &mut Default::default()))
            .collect();

        Some(Expr::Net(Net {
            lhs: Some(lhs_agent),
            rhs: Some(rhs_agent),
        }))
    }

    pub fn readback_elem(&self, p: Ptr, seen: &mut BTreeSet<Ptr>) -> Option<Port> {
        if seen.contains(&p) {
            return None;
        }

        seen.insert(p);

        let elem = self.iter_deref(GlobalPtr::MemPtr(p)).last()?;

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
                        .filter_map(|p| self.readback_elem(p.get_src_pos()?, seen))
                        .collect::<Vec<_>>(),
                }))
            }
            _ => None,
        }?;

        Some(build)
    }

    pub fn step(&mut self) -> Result<(), Error> {
        let next_elem = if let StackElem::Instr(o) = self
            .src
            .get(self.pos)
            .cloned()
            .ok_or(Error::NothingToAdvance)?
        {
            o
        } else {
            self.pos += 1;

            return Ok(());
        };

        let stack_snapshot = self.stack.clone();

        tracing::trace!(
            "attempting op execution {} with args {:?} at line {}",
            next_elem,
            stack_snapshot,
            self.pos,
        );

        let res = (|| -> Option<()> {
            let res = match next_elem.as_ref() {
                &Op::Substitute => {
                    while self.stack.len() >= 2 {
                        let (v1, v2) = (self.stack.pop_back()?, self.stack.pop_back()?);

                        let (dest, src) = if let (Some(dest), Some(src)) =
                            (v1.as_ptr()?.as_mem_ptr(), v2.as_ptr()?.as_mem_ptr())
                        {
                            (dest, src)
                        } else {
                            self.stack.push_back(v2);
                            self.stack.push_back(v1);

                            break;
                        };

                        let to_substitute_ptr = dest;
                        let to_substitute_with = self.iter_deref(GlobalPtr::MemPtr(src)).next()?;

                        *self.src.0.get_mut(to_substitute_ptr)? = to_substitute_with;

                        self.refresh_redex_bag();
                    }

                    Some(())
                }
                &Op::PushSubstitutionPositions => {
                    let parent_tree = self.stack.pop_back()?.as_ptr()?.as_mem_ptr()?;
                    let child_tree = self.stack.pop_back()?.as_ptr()?.as_mem_ptr()?;

                    let positions = self.subset_tree_positions(child_tree, parent_tree);

                    if let Some(positions) = positions {
                        for Substitution { src, dest } in positions {
                            self.stack.push_back(StackElem::Ptr(dest));
                            self.stack.push_back(StackElem::Ptr(src));
                        }
                    } else {
                        self.stack.push_back(StackElem::None);
                    }

                    Some(())
                }
                &Op::PushMatchingRule => {
                    let ptr_lhs = self.stack.pop_back()?.into_ptr()?.into_mem_ptr()?;

                    let agent_a = self.src.0.get(ptr_lhs)?.as_agent()?;

                    let ptr_rhs = agent_a.ports.get(0)?.as_agent_ptr()?.mem_pos;
                    let agent_b = self.src.0.get(ptr_rhs)?.as_agent()?;

                    let agent_a_name = self.src.get(agent_a.name.as_mem_ptr()?)?.as_ident()?;
                    let agent_b_name = self.src.get(agent_b.name.as_mem_ptr()?)?.as_ident()?;

                    let sig_a = self.types.get(&Type(agent_a_name.to_owned()))?;

                    let to_match = if sig_a.get(0)?.as_output().is_some() {
                        (ptr_lhs, agent_a, agent_a_name)
                    } else {
                        (ptr_rhs, agent_b, agent_b_name)
                    };

                    let agents = self
                        .src
                        .0
                        .iter()
                        .enumerate()
                        .filter_map(|(i, elem)| Some((i, elem.as_agent()?)));
                    let redexed_agents = agents.filter_map(|(mem_pos, agent)| {
                        let a = agent;
                        let b_port_ptr = agent.ports.get(0)?.as_agent_ptr()?;
                        let b = self.src.get(b_port_ptr.mem_pos)?.as_agent()?;

                        if b_port_ptr.port != Some(0) {
                            return None;
                        }

                        Some(((mem_pos, a), (b_port_ptr.mem_pos, b)))
                    });
                    let named_typed_agents =
                        redexed_agents.filter_map(|((a_pos, a), (b_pos, b))| {
                            let name_a = self.src.get(a.name.as_mem_ptr()?)?.as_ident()?;
                            let name_b = self.src.get(b.name.as_mem_ptr()?)?.as_ident()?;

                            let ty_a = self.types.get(&Type(name_a.to_owned()))?;
                            let ty_b = self.types.get(&Type(name_a.to_owned()))?;

                            Some(((ty_a, name_a, a_pos, a), (ty_b, name_b, b_pos, b)))
                        });
                    let out_first = named_typed_agents.filter_map(
                        |((ty_a, name_a, a_pos, a), (ty_b, name_b, b_pos, b))| {
                            if ty_a.get(0)?.as_output().is_some() {
                                Some(((ty_a, name_a, a_pos, a), (ty_b, name_b, b_pos, b)))
                            } else {
                                Some(((ty_b, name_b, b_pos, b), (ty_a, name_a, a_pos, a)))
                            }
                        },
                    );
                    let name_matching_rules =
                        out_first.filter(|((_, name_a, _, _), (_, name_b, _, _))| {
                            BTreeSet::from_iter([*name_a, *name_b])
                                == BTreeSet::from_iter([agent_a_name, agent_b_name])
                        });

                    // The structure of the rule must be identical, except
                    // for the variables. These can be bound to whatever
                    let mut matching_rules =
                        name_matching_rules.filter_map(|((_, _, pos, _), _)| {
                            Some((pos, self.subset_tree_positions(to_match.0, pos)?))
                        });

                    if let Some((pos, _)) = matching_rules.next() {
                        self.stack.push_back(StackElem::Ptr(GlobalPtr::MemPtr(pos)));
                    } else {
                        self.stack.push_back(StackElem::None);
                    }

                    Some(())
                }
                &Op::Pop => {
                    let _ = self.stack.pop_back()?;

                    Some(())
                }
                &Op::CloneNet => {
                    let to_clone = self.stack.pop_back()?.into_ptr()?.into_mem_ptr()?;
                    let ptr = self.clone_tree(to_clone)?;

                    self.stack.push_back(StackElem::Ptr(GlobalPtr::MemPtr(ptr)));

                    Some(())
                }
                &Op::QueueRedex => {
                    let lhs_ptr = self.stack.pop_back()?.into_ptr()?.into_mem_ptr()?;
                    let lhs_agent = self
                        .iter_deref(GlobalPtr::MemPtr(lhs_ptr))
                        .next()?
                        .into_agent()?;

                    let rhs_ptr = lhs_agent.ports.get(0)?.as_agent_ptr()?.mem_pos;

                    self.redex_bag.push_back((lhs_ptr, rhs_ptr));

                    Some(())
                }
                &Op::PushRedex => {
                    if let Some(redex) = self.redex_bag.pop_back() {
                        self.stack
                            .push_back(StackElem::Ptr(GlobalPtr::MemPtr(redex.0)));
                    } else {
                        self.stack.push_back(StackElem::None);
                    }

                    Some(())
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

                    Some(())
                }
                &Op::PortPtr => {
                    let port = self.stack.pop_back()?.into_ptr()?.into_agent_ptr()?;
                    self.stack
                        .push_back(StackElem::Ptr(GlobalPtr::MemPtr(port.mem_pos)));

                    Some(())
                }
                &Op::Copy => {
                    let to_cpy = self.stack.pop_back()?;

                    self.stack.push_back(to_cpy.clone());
                    self.stack.push_back(to_cpy);

                    Some(())
                }
                &Op::Swap3 => {
                    let a = self.stack.pop_back()?;
                    let b = self.stack.pop_back()?;
                    let c = self.stack.pop_back()?;

                    self.stack.push_back(a);
                    self.stack.push_back(b);
                    self.stack.push_back(c);

                    Some(())
                }
                &Op::Flip => {
                    let a = self.stack.pop_back()?;
                    let b = self.stack.pop_back()?;

                    self.stack.push_back(a);
                    self.stack.push_back(b);

                    Some(())
                }
                &Op::PushStack(ref elem) => {
                    self.stack.push_back(elem.clone());

                    Some(())
                }
                &Op::Load => {
                    let elem = self.stack.pop_back()?;
                    let ptr = elem.as_ptr()?;
                    let loaded = self.iter_deref(*ptr).last()?;

                    self.stack.push_back(loaded);

                    Some(())
                }
                &Op::LoadMem => {
                    let elem = self.stack.pop_back()?;
                    let ptr = elem.as_ptr()?;

                    if let Some(loaded) = self.mem.get(ptr.as_mem_ptr()?) {
                        self.stack.push_back(loaded.clone());
                    } else {
                        self.stack.push_back(StackElem::None);
                    }

                    Some(())
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

                    Some(())
                }
                &Op::PushRes => {
                    let v = self
                        .stack
                        .pop_back()
                        .and_then(|elem| elem.as_ptr().cloned())?;

                    let lhs = self
                        .stack
                        .pop_back()
                        .and_then(|elem| elem.as_ptr().cloned())?;
                    let lhs_elem = self.iter_deref(lhs).next()?;
                    let lhs_agent = lhs_elem.as_agent()?;
                    let rhs = lhs_agent.ports.get(0)?;

                    let relevant_ptr = |ptr| {
                        let elem = self.iter_deref(ptr).next()?;

                        match elem {
                            StackElem::Var(name) => {
                                let name_elem = self.iter_deref(GlobalPtr::MemPtr(name)).next()?;
                                let name = name_elem.as_ident()?;

                                Some(RedexElem::Var {
                                    name: name.to_owned(),
                                })
                            }
                            StackElem::Agent(Agent { name, .. }) => {
                                let name_elem = self.iter_deref(name).next()?;
                                let name = name_elem.as_ident()?;

                                Some(RedexElem::Agent {
                                    name: name.to_owned(),
                                })
                            }
                            _ => None,
                        }
                    };

                    let tree_lhs = self.iter_tree(lhs)?.filter_map(relevant_ptr);
                    let tree_rhs = self.iter_tree(*rhs)?.filter_map(relevant_ptr);

                    let result = self.readback(v)?;

                    let path = Rc::new(tree_lhs.zip(tree_rhs).collect::<Vec<_>>());

                    self.results.insert(path.clone(), result);
                    self.results_ord.push(path);

                    Some(())
                }
                &Op::Debug => {
                    let p = self.stack.pop_back()?;

                    tracing::debug!("{}", p);

                    Some(())
                }
                &Op::DebugMem => {
                    tracing::debug!("{:?}", self.mem);

                    Some(())
                }
                &Op::Cmp => {
                    let (deref_a, deref_b) = (self.stack.pop_back(), self.stack.pop_back());

                    self.stack.push_back(StackElem::Bool(deref_a == deref_b));

                    Some(())
                }
                &Op::GoTo => {
                    let pos = self
                        .stack
                        .pop_back()
                        .and_then(|elem| elem.as_ptr()?.as_mem_ptr())?;
                    self.pos = pos;

                    return Some(());
                }
                Op::GoToEq => {
                    let pos = self.stack.pop_back()?.as_ptr()?.as_mem_ptr()?;
                    let a = self.stack.pop_back()?;
                    let b = self.stack.pop_back()?;

                    if a != b {
                        self.pos += 1;

                        return Some(());
                    }

                    self.pos = pos;

                    return Some(());
                }
                Op::GoToNeq => {
                    let pos = self.stack.pop_back()?.as_ptr()?.as_mem_ptr()?;
                    let a = self.stack.pop_back()?;
                    let b = self.stack.pop_back()?;

                    if a == b {
                        self.pos += 1;

                        return Some(());
                    }

                    self.pos = pos;

                    return Some(());
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

                            Some(())
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

                    Some(())
                }
                &Op::IncrPtr => {
                    let offset = self.stack.pop_back().and_then(|elem| elem.into_offset())?;
                    let recent_ptr = self.stack.pop_back().and_then(|elem| elem.into_ptr())?;
                    self.stack
                        .push_back(StackElem::Ptr(recent_ptr.add_offset(offset)?));

                    Some(())
                }
            };

            self.pos += 1;

            res
        })()
        .ok_or(Error::CouldNotAdvance {
            op: *next_elem,
            args: stack_snapshot.clone().into(),
        });

        res.map(|_| ())
    }

    pub fn step_to_end(&mut self) -> Result<impl Iterator<Item = &Expr>, Error> {
        while self.pos < self.src.len() {
            self.step()?;
        }

        Ok(self.results_ord.iter().filter_map(|k| self.results.get(k)))
    }
}

pub struct DerefVisitor<'a> {
    pos: Option<GlobalPtr>,
    view: &'a State,
    seen: BTreeSet<GlobalPtr>,
}

impl<'a> DerefVisitor<'a> {
    pub fn new(view: &'a State, pos: GlobalPtr) -> Self {
        Self {
            pos: Some(pos),
            seen: Default::default(),
            view,
        }
    }
}

impl Iterator for DerefVisitor<'_> {
    type Item = StackElem;

    fn next(&mut self) -> Option<Self::Item> {
        let curr_ptr = self.pos?;

        if self.seen.contains(&curr_ptr) {
            return None;
        }

        self.seen.insert(curr_ptr);

        let curr = {
            match curr_ptr {
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
        let mut to_visit = self
            .to_visit
            .drain(..)
            .skip_while(|x| self.seen.contains(x))
            .collect::<VecDeque<_>>();
        let curr_ptr = to_visit.pop_front()?;
        self.to_visit = to_visit;

        if let GlobalPtr::AgentPtr(ptr) = curr_ptr {
            self.to_visit.push_front(GlobalPtr::MemPtr(ptr.mem_pos));
        }

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

#[cfg(test)]
mod test {
    use crate::{
        bytecode2 as bc, heuristics as heur,
        parser::parser_lafont::{lexer, parser},
    };
    use chumsky::Parser;

    #[test_log::test]
    fn test_iter_tree() {
        let cases = ["type nat
             symbol Z: nat+
             symbol Add: nat-, nat-, nat+
             Add(x, x) >< Z()"];

        for case in cases {
            let lexed = lexer()
                .parse(case)
                .unwrap()
                .into_iter()
                .flatten()
                .collect::<Vec<_>>();
            let parsed = parser().parse(lexed).unwrap();

            let (typed, _) = heur::parse_typed_program(parsed);

            let program = bc::compilation::compile(typed.clone()).unwrap();

            let state = bc::vm::State::new(program, typed.symbol_declarations_for);
            let ptrs = state.iter_tree(bc::GlobalPtr::MemPtr(5)).unwrap();

            let mut elems = ptrs.filter_map(|ptr| state.iter_deref(ptr).next());
            assert!(elems
                .find(|elem| matches!(elem, bc::StackElem::Var(_)))
                .is_some());
        }
    }
}
