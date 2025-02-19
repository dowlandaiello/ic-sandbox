use super::CombinatorBuilder as AbstractCombinatorBuilder;
use crate::parser_sk::Expr as SkExpr;
use ast_ext::{TreeCursor, TreeVisitor};
use inetlib::parser::{
    ast_combinators::{Constructor, Duplicator, Eraser, Expr as AstExpr, Port as AstPort, Var},
    ast_lafont::Ident,
    naming::NameIter,
};
use std::{cell::RefCell, cmp::Ordering, collections::BTreeMap, iter, rc::Rc};

pub type Port = (usize, OwnedNetBuilder);

#[derive(Debug, Clone)]
pub(crate) struct OwnedNetBuilder(pub Rc<RefCell<NamedBuilder>>);

impl Ord for OwnedNetBuilder {
    fn cmp(&self, other: &Self) -> Ordering {
        self.0.borrow().name.cmp(&other.0.borrow().name)
    }
}

impl PartialOrd for OwnedNetBuilder {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Eq for OwnedNetBuilder {}

impl PartialEq for OwnedNetBuilder {
    fn eq(&self, other: &Self) -> bool {
        self.0.as_ptr() == other.0.as_ptr()
    }
}

impl TreeCursor<OwnedNetBuilder> for OwnedNetBuilder {
    fn hash(&self) -> usize {
        self.0.borrow().name
    }

    fn value(&self) -> OwnedNetBuilder {
        self.clone()
    }

    fn children(&self) -> Box<dyn Iterator<Item = Self>> {
        Box::new(
            self.0
                .borrow()
                .builder
                .iter_ports()
                .filter_map(|x| x)
                .map(|(_, p)| p)
                .cloned()
                .collect::<Vec<_>>()
                .into_iter(),
        )
    }
}

impl AbstractCombinatorBuilder for OwnedNetBuilder {
    type CPort = AstPort;
    type EExpr = SkExpr;

    fn decombinate(p: &AstPort) -> Option<SkExpr> {
        if let Some(root_expr) =
            Self::decombinate_expr(&p, CombinatorBuilder::K { primary_port: None })
                .then(|| SkExpr::K(None, None))
                .or_else(|| {
                    Self::decombinate_expr(&p, CombinatorBuilder::S { primary_port: None })
                        .then(|| SkExpr::S(None, None, None))
                })
        {
            return Some(root_expr);
        }

        // Application requires an active pair
        if let Some((lhs, rhs)) = p.try_as_active_pair() {
            tracing::trace!("found application {}", lhs.1);

            fn args(root: Option<&AstPort>) -> Option<Vec<AstPort>> {
                match &*root?.borrow() {
                    AstExpr::Constr(Constructor { aux_ports, .. }) => {
                        let mut next_args = aux_ports.as_ref().iter();
                        let (next, arg) = (next_args.next(), next_args.next());

                        let mut res =
                            vec![arg.map(|x| x.as_ref().map(|(_, x)| x)).flatten()?.clone()];

                        if let Some(others) =
                            args(next.map(|x| x.as_ref().map(|(_, x)| x)).flatten())
                        {
                            res.extend(others);
                        }

                        Some(res)
                    }
                    _ => None,
                }
            }

            let args = args(Some(&rhs.1)).expect("missing application args");

            tracing::trace!(
                "application has arg {}",
                args.iter()
                    .map(|x| x.to_string())
                    .collect::<Vec<_>>()
                    .join(", ")
            );

            lhs.1.borrow_mut().set_primary_port(None);

            let mut to_call_dec =
                Self::decombinate(&lhs.1).expect("combinator call missing valid applicand");

            for arg in args {
                to_call_dec = to_call_dec.with_push_argument(Some(Box::new(
                    Self::decombinate(&arg).expect("invalid argument #1"),
                )));
            }

            return Some(to_call_dec);
        }

        Self::decombinate_expr(p, CombinatorBuilder::K { primary_port: None })
            .then(|| SkExpr::K(None, None))
            .or_else(|| {
                Self::decombinate_expr(p, CombinatorBuilder::S { primary_port: None })
                    .then(|| SkExpr::S(None, None, None))
            })
            .or_else(|| unreachable!())
    }

    fn combinate(&self, names: &NameIter) -> Self::CPort {
        // Normalize ZN_1 agents
        self.clone()
            .iter_tree()
            .filter_map(|x| {
                if let CombinatorBuilder::ZN {
                    primary_port,
                    aux_ports,
                } = x.0.borrow().builder.clone()
                {
                    Some((primary_port, aux_ports))
                } else {
                    None
                }
            })
            .for_each(|(primary_port, aux_ports)| {
                // Need to wire the primary and aux ports
                let (p, aux) = primary_port
                    .as_ref()
                    .cloned()
                    .zip(aux_ports.get(0).cloned().flatten())
                    .expect("ZN_1 expansion must have set primary and aux ports");

                Self::connect(p, aux);
            });

        let mut agents_for_id: BTreeMap<usize, AstPort> = self
            .clone()
            .iter_tree()
            .filter_map(|x| match &x.0.borrow().builder {
                // ZN_1 itself will never be combinated, and if it is found,
                // it must have attached ports, otherwise we can ignore it.
                // ZN_1 will be handled during wiring
                CombinatorBuilder::ZN { aux_ports, .. } => {
                    assert_eq!(aux_ports.len(), 1);

                    None
                }
                CombinatorBuilder::Constr { .. } => Some((
                    x.0.borrow().name,
                    AstExpr::Constr(Constructor::new()).into_port(names),
                )),
                CombinatorBuilder::Era { .. } => Some((
                    x.0.borrow().name,
                    AstExpr::Era(Eraser::new()).into_port(names),
                )),
                CombinatorBuilder::Dup { .. } => Some((
                    x.0.borrow().name,
                    AstExpr::Dup(Duplicator::new()).into_port(names),
                )),
                CombinatorBuilder::Var { name, .. } => Some((
                    x.0.borrow().name,
                    AstExpr::Var(Var {
                        name: Ident(name.clone()),
                        port: None,
                    })
                    .into_port(names),
                )),
                x => {
                    tracing::trace!("attempted to build {}", x.name());

                    unreachable!()
                }
            })
            .collect();

        self.clone().iter_tree().for_each(|x| {
            let id = x.0.borrow().name;

            let builder = &x.0.borrow().builder;

            if matches!(builder, CombinatorBuilder::ZN { .. }) {
                return;
            }

            if let Some((port, p)) = builder.primary_port().clone() {
                let other_id = p.0.borrow().name;
                let other_node = agents_for_id.get(&other_id).cloned();

                let node = agents_for_id.get_mut(&id).unwrap();

                node.borrow_mut()
                    .set_primary_port(other_node.map(|p| (*port, p)));
            }

            let mut aux_ports = builder.iter_aux_ports().map(|p| {
                let (port, p) = p?;

                let other_id = p.0.borrow().name;
                let other_node = agents_for_id.get(&other_id)?.clone();

                Some((*port, other_node))
            });
            let mut all_aux_ports = [None, None];

            if let Some(x) = aux_ports.next() {
                all_aux_ports[0] = x;
            }

            if let Some(x) = aux_ports.next() {
                all_aux_ports[1] = x;
            }

            let node = agents_for_id.get_mut(&id).unwrap();

            node.borrow_mut().set_aux_ports(all_aux_ports);
        });

        let active_pair_or_roots = agents_for_id.values();
        active_pair_or_roots
            .clone()
            .filter(|x| x.try_as_active_pair().is_some())
            .next()
            .or_else(|| {
                active_pair_or_roots
                    .clone()
                    .filter(|x| {
                        let bor = x.borrow();
                        let pp = bor.primary_port();

                        bor.is_agent() || pp.map(|p| p.1.borrow().is_var()).unwrap_or(true)
                    })
                    .next()
            })
            .or_else(|| active_pair_or_roots.filter(|x| x.borrow().is_var()).next())
            .expect("no root for combinated expression")
            .clone()
    }

    fn expand_step(&self, names: &NameIter) -> Self {
        let builder = self.cloned();

        tracing::trace!("begin expansion {}", self.0.borrow().builder.name());

        let new_root = match &builder {
            CombinatorBuilder::Z4 {
                primary_port,
                aux_ports,
            } => {
                let root_ref = self.update_with(|_| CombinatorBuilder::Constr {
                    primary_port: None,
                    aux_ports: [const { None }; 2],
                });

                let root_parent = OwnedNetBuilder::new(
                    CombinatorBuilder::Constr {
                        primary_port: None,
                        aux_ports: [const { None }; 2],
                    },
                    names,
                );

                let root_parent_parent = OwnedNetBuilder::new(
                    CombinatorBuilder::Constr {
                        primary_port: None,
                        aux_ports: [const { None }; 2],
                    },
                    names,
                );

                Self::connect((1, root_ref.clone()), (0, root_parent.clone()));
                Self::connect((1, root_parent.clone()), (0, root_parent_parent.clone()));

                self.clone().iter_tree().for_each(|x| println!("{:?}", x));

                if let Some(p) = &primary_port {
                    Self::connect((0, root_ref.clone()), p.clone());
                }

                if let Some(p) = &aux_ports[0] {
                    Self::connect(p.clone(), (1, root_parent_parent.clone()));
                }

                if let Some(p) = &aux_ports[1] {
                    Self::connect(p.clone(), (2, root_parent_parent.clone()));
                }

                if let Some(p) = &aux_ports[2] {
                    Self::connect(p.clone(), (2, root_parent.clone()));
                }

                if let Some(p) = &aux_ports[3] {
                    Self::connect(p.clone(), (2, root_ref.clone()));
                }

                root_ref.clone()
            }
            CombinatorBuilder::ZN {
                primary_port,
                aux_ports,
            } => {
                tracing::trace!("expanding Z of arity {}", aux_ports.len());

                // We cannot expand Z_1, since all expansions create new agents,
                // and cannot remove agents, which Z_1 expansion does.
                // See combinate() for implementation
                match aux_ports.len() {
                    1 => self.clone(),
                    2 => {
                        self.update_with(|_| CombinatorBuilder::Constr {
                            primary_port: primary_port.clone(),
                            aux_ports: aux_ports.clone().try_into().unwrap(),
                        });

                        self.clone()
                    }
                    n => {
                        let parent_ports =
                            aux_ports.iter().cloned().take(n - 1).collect::<Vec<_>>();

                        let parent = OwnedNetBuilder::new(
                            CombinatorBuilder::ZN {
                                primary_port: None,
                                aux_ports: parent_ports,
                            },
                            names,
                        );

                        for i in 0..(n - 1) {
                            self.clone()
                                .rewrite_conns((i + 1, self.clone()), (i + 1, parent.clone()));
                        }

                        let constr_child = self.update_with(|_| CombinatorBuilder::Constr {
                            primary_port: primary_port.clone(),
                            aux_ports: [Some((0, parent.clone())), aux_ports[n - 1].clone()],
                        });

                        self.clone()
                            .rewrite_conns((n, self.clone()), (2, constr_child.clone()));

                        Self::connect((1, constr_child.clone()), (0, parent.clone()));

                        parent.expand_step(names);

                        self.clone()
                    }
                }
            }
            CombinatorBuilder::D {
                ref primary_port,
                aux_port,
            } => {
                tracing::trace!("expanding D");

                let dup = OwnedNetBuilder::new(
                    CombinatorBuilder::Dup {
                        primary_port: None,
                        aux_ports: [const { None }; 2],
                    },
                    names,
                );
                let root = CombinatorBuilder::ZN {
                    primary_port: primary_port.clone(),
                    aux_ports: vec![None; 4],
                };

                self.update_with(|_| root);

                // Aux <-> root
                if let Some((port, aux)) = aux_port {
                    Self::connect((*port, aux.clone()), (4, self.clone()));
                }

                // Dup <-> root
                Self::connect((1, dup.clone()), (1, self.clone()));
                Self::connect((2, dup.clone()), (2, self.clone()));
                Self::connect((0, dup.clone()), (3, self.clone()));

                self.expand_step(names);

                self.clone()
            }
            CombinatorBuilder::K { primary_port } => {
                tracing::trace!("expanding K @ 0x{}", self.0.borrow().name);

                let d = OwnedNetBuilder::new(
                    CombinatorBuilder::D {
                        primary_port: None,
                        aux_port: None,
                    },
                    names,
                );
                let e = OwnedNetBuilder::new(CombinatorBuilder::Era { primary_port: None }, names);
                let root = CombinatorBuilder::ZN {
                    primary_port: primary_port.clone(),
                    aux_ports: vec![
                        Some((1, d.clone())),
                        Some((0, e.clone())),
                        Some((0, d.clone())),
                    ],
                };
                let root_ref = self;

                if let Some(p) = primary_port {
                    Self::connect((0, self.clone()), p.clone());
                }

                Self::connect((1, self.clone()), (1, d.clone()));
                Self::connect((3, self.clone()), (0, d.clone()));
                Self::connect((2, self.clone()), (0, e.clone()));

                self.update_with(|_| root);

                d.expand_step(names);
                root_ref.expand_step(names);
                d.expand_step(names);

                self.clone()
            }
            CombinatorBuilder::S { primary_port } => {
                tracing::trace!("expanding S");

                let top_left_z = OwnedNetBuilder::new(
                    CombinatorBuilder::ZN {
                        primary_port: primary_port.clone(),
                        aux_ports: vec![None; 4],
                    },
                    names,
                );
                let middle_left_z = OwnedNetBuilder::new(
                    CombinatorBuilder::ZN {
                        primary_port: None,
                        aux_ports: vec![None; 4],
                    },
                    names,
                );

                let right_bottom_z_ref = self;

                let d = OwnedNetBuilder::new(
                    CombinatorBuilder::D {
                        primary_port: None,
                        aux_port: None,
                    },
                    names,
                );

                let left_middle_constr = OwnedNetBuilder::new(
                    CombinatorBuilder::Constr {
                        primary_port: None,
                        aux_ports: [const { None }; 2],
                    },
                    names,
                );
                let middle_constr = OwnedNetBuilder::new(
                    CombinatorBuilder::Constr {
                        primary_port: None,
                        aux_ports: [const { None }; 2],
                    },
                    names,
                );
                let bottom_middle_right_constr = OwnedNetBuilder::new(
                    CombinatorBuilder::Constr {
                        primary_port: None,
                        aux_ports: [const { None }; 2],
                    },
                    names,
                );

                let dup = OwnedNetBuilder::new(
                    CombinatorBuilder::Dup {
                        primary_port: None,
                        aux_ports: [const { None }; 2],
                    },
                    names,
                );

                // Connect bottom z
                let right_bottom_z = CombinatorBuilder::ZN {
                    primary_port: primary_port.clone(),
                    aux_ports: vec![None; 4],
                };

                // Top left  Z conns
                Self::connect((0, top_left_z.clone()), (3, right_bottom_z_ref.clone()));
                Self::connect((1, top_left_z.clone()), (4, top_left_z.clone()));
                Self::connect((2, top_left_z.clone()), (2, middle_left_z.clone()));
                Self::connect((3, top_left_z.clone()), (3, middle_left_z.clone()));

                // Middle left Z conns
                Self::connect(
                    (0, middle_left_z.clone()),
                    (2, bottom_middle_right_constr.clone()),
                );
                Self::connect((1, middle_left_z.clone()), (0, left_middle_constr.clone()));
                Self::connect((4, middle_left_z.clone()), (1, left_middle_constr.clone()));

                // Bottom right Z conns
                if let Some(p) = primary_port {
                    Self::connect((0, right_bottom_z_ref.clone()), p.clone());
                }

                Self::connect(
                    (1, right_bottom_z_ref.clone()),
                    (1, bottom_middle_right_constr.clone()),
                );
                Self::connect((2, right_bottom_z_ref.clone()), (0, dup.clone()));
                Self::connect((4, right_bottom_z_ref.clone()), (0, d.clone()));

                // Dup conns
                Self::connect((1, dup.clone()), (2, left_middle_constr.clone()));
                Self::connect((2, dup.clone()), (2, middle_constr.clone()));

                // D conns
                Self::connect((1, d.clone()), (0, middle_constr.clone()));

                // Middle constr conns
                Self::connect(
                    (1, middle_constr.clone()),
                    (0, bottom_middle_right_constr.clone()),
                );
                Self::connect((2, middle_constr.clone()), (2, dup.clone()));

                self.update_with(|_| right_bottom_z);

                top_left_z.expand_step(names);
                middle_left_z.expand_step(names);
                d.expand_step(names);
                d.expand_step(names);
                right_bottom_z_ref.expand_step(names);

                self.clone()
            }
            CombinatorBuilder::Var { .. } => {
                tracing::trace!("expanding var");

                self.clone()
            }
            CombinatorBuilder::Constr { .. } => {
                tracing::trace!("expanding Constr");

                self.clone()
            }
            CombinatorBuilder::Era { .. } => {
                tracing::trace!("expanding Era");

                self.clone()
            }
            CombinatorBuilder::Dup { .. } => {
                tracing::trace!("expanding Dup");

                self.clone()
            }
        };

        #[cfg(test)]
        self.checksum();

        tracing::trace!("expansion finished");

        new_root
    }
}

impl OwnedNetBuilder {
    pub(crate) fn rewrite_conns(self, src: Port, dest: Port) {
        self.iter_tree().for_each(|x| {
            x.0.borrow_mut()
                .builder
                .iter_ports_mut()
                .filter_map(|x| x)
                .filter(|conn| **conn == src)
                .for_each(|conn| {
                    tracing::trace!("rewriting {:?}", (conn.0, conn.1 .0.as_ptr()));

                    *conn = dest.clone()
                })
        });
    }

    pub(crate) fn connect(lhs: Port, rhs: Port) {
        lhs.1
            .update_with(|builder| builder.clone().set_port_i(lhs.0, Some(rhs.clone())));
        rhs.1
            .update_with(|builder| builder.clone().set_port_i(rhs.0, Some(lhs.clone())));
    }

    pub(crate) fn make_root(self, names: &NameIter) -> Self {
        let next_port_idx = {
            let builder = &self.0.borrow().builder;

            builder
                .next_empty_port()
                .unwrap_or_else(|| builder.len_ports())
        };

        let v = OwnedNetBuilder::new(
            CombinatorBuilder::Var {
                name: names.next_var_name(),
                primary_port: None,
            },
            names,
        );

        Self::connect((next_port_idx, self.clone()), (0, v.clone()));

        self
    }

    /// Finds all mismatched ports in the tree (i.e., one agent connected to another agent that is not connected to its parent)
    pub(crate) fn checksum(&self) {
        self.clone().iter_tree().for_each(|x| {
            x.0.borrow()
                .builder
                .iter_ports()
                .filter_map(|x| x)
                .for_each(|(port, p)| {
                    tracing::trace!("checksum context: {:?} {:?}", x, p);

                    assert_eq!(
                        p.0.borrow()
                            .builder
                            .iter_ports()
                            .nth(*port)
                            .unwrap()
                            .unwrap()
                            .1
                             .0
                            .borrow()
                            .name,
                        x.0.borrow().name
                    );
                });
        });
    }

    pub(crate) fn encode(self, names: &NameIter) -> Self {
        self.expand_step(names);

        let dup_refs = self
            .clone()
            .iter_tree()
            .filter(|p| matches!(&p.0.borrow().builder, CombinatorBuilder::Dup { .. }))
            .collect::<Vec<_>>();
        let n_dup_refs = dup_refs.len();

        let mut dup_ref_ports = dup_refs
            .iter()
            .map(|x| {
                let mut auxes =
                    x.0.borrow()
                        .builder
                        .iter_aux_ports()
                        .map(|x| x.cloned())
                        .collect::<Vec<_>>();
                auxes.push(x.0.borrow().builder.primary_port().cloned());

                auxes
            })
            .collect::<Vec<_>>();

        let new_root = OwnedNetBuilder::new(
            CombinatorBuilder::ZN {
                primary_port: self.0.borrow().builder.primary_port().cloned(),
                aux_ports: vec![None; 4],
            },
            names,
        );

        let empty_port = self
            .0
            .borrow()
            .builder
            .iter_ports()
            .position(|x| x.is_none())
            .unwrap_or(0);

        Self::connect((empty_port, self.clone()), (4, new_root.clone()));

        let z_combs: [OwnedNetBuilder; 3] = (0..3)
            .map(|i| {
                let comb = OwnedNetBuilder::new(CombinatorBuilder::mk_z_n(n_dup_refs), names);

                Self::connect((1 + i, new_root.clone()), (0, comb.clone()));

                comb
            })
            .collect::<Vec<_>>()
            .try_into()
            .unwrap();

        for ports in dup_ref_ports.iter_mut() {
            let (p1, p2, p3) = (ports.remove(0), ports.remove(0), ports.remove(0));

            let ins_port_1 = z_combs[0].0.borrow().builder.next_empty_port().unwrap();

            if let Some(p) = p1 {
                Self::connect(p, (ins_port_1, z_combs[0].clone()));
            }

            let ins_port_2 = z_combs[1].0.borrow().builder.next_empty_port().unwrap();

            if let Some(p) = p2 {
                Self::connect(p, (ins_port_2, z_combs[1].clone()));
            }

            let ins_port_3 = z_combs[2].0.borrow().builder.next_empty_port().unwrap();

            if let Some(p) = p3 {
                Self::connect(p, (ins_port_3, z_combs[2].clone()));
            }
        }

        for comb in z_combs {
            comb.expand_step(names);
        }

        new_root.checksum();

        new_root
    }

    pub(crate) fn iter_tree(self) -> impl Iterator<Item = OwnedNetBuilder> {
        TreeVisitor::new(self)
    }

    pub(crate) fn new(b: CombinatorBuilder, names: &NameIter) -> Self {
        Self(Rc::new(RefCell::new(b.to_named(names))))
    }

    fn decombinate_expr(p: &AstPort, cmp: CombinatorBuilder) -> bool {
        let old_primary_port = p.unroot();

        let mut names = Default::default();

        let k_tree = Self::new(cmp.clone(), &mut names);
        k_tree.expand_step(&mut names);

        let combinated = k_tree.make_root(&mut names).combinate(&mut names).orient();
        combinated.unroot();

        tracing::trace!("found {}", p);
        tracing::trace!("found {}", combinated);

        if combinated.alpha_eq(&p) {
            tracing::trace!("found {:?}", cmp);

            true
        } else {
            p.borrow_mut().set_primary_port(old_primary_port);

            false
        }
    }

    pub(crate) fn cloned(&self) -> CombinatorBuilder {
        self.0.borrow().clone().builder
    }

    pub(crate) fn update_with(
        &self,
        f: impl FnOnce(&CombinatorBuilder) -> CombinatorBuilder,
    ) -> &Self {
        self.0.replace_with(|val| {
            let mut new_val = val.clone();

            let new_builder = f(&val.builder);
            new_val.builder = new_builder;

            new_val
        });

        self
    }
}

#[derive(Debug, Clone)]
pub(crate) struct NamedBuilder {
    pub(crate) name: usize,
    pub(crate) builder: CombinatorBuilder,
}

impl AsRef<CombinatorBuilder> for NamedBuilder {
    fn as_ref(&self) -> &CombinatorBuilder {
        &self.builder
    }
}

impl AsMut<CombinatorBuilder> for NamedBuilder {
    fn as_mut(&mut self) -> &mut CombinatorBuilder {
        &mut self.builder
    }
}

#[derive(Clone)]
pub(crate) enum CombinatorBuilder {
    Z4 {
        primary_port: Option<Port>,
        aux_ports: [Option<Port>; 4],
    },
    ZN {
        primary_port: Option<Port>,
        aux_ports: Vec<Option<Port>>,
    },
    D {
        primary_port: Option<Port>,
        aux_port: Option<Port>,
    },
    K {
        primary_port: Option<Port>,
    },
    S {
        primary_port: Option<Port>,
    },
    Var {
        name: String,
        primary_port: Option<Port>,
    },
    Constr {
        primary_port: Option<Port>,
        aux_ports: [Option<Port>; 2],
    },
    Dup {
        primary_port: Option<Port>,
        aux_ports: [Option<Port>; 2],
    },
    Era {
        primary_port: Option<Port>,
    },
}

impl std::fmt::Debug for CombinatorBuilder {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let ports = self.iter_ports();
        let ports_debug = ports
            .skip(1)
            .map(|p| {
                p.map(|(port, p)| {
                    format!(
                        "{} @ 0x{} in {}",
                        p.0.borrow().builder.name().to_owned(),
                        p.0.borrow().name,
                        port,
                    )
                })
            })
            .collect::<Vec<_>>();

        f.debug_struct("CombinatorBuilder")
            .field("name", &self.name())
            .field(
                "primary_port",
                &self.iter_ports().next().map(|p| {
                    p.map(|(port, p)| {
                        format!(
                            "{} @ 0x{} in {}",
                            p.0.borrow().builder.name().to_owned(),
                            p.0.borrow().name,
                            port,
                        )
                    })
                }),
            )
            .field("aux_ports", &ports_debug)
            .finish()
    }
}

impl CombinatorBuilder {
    pub(crate) fn mk_z_n(n: usize) -> Self {
        Self::ZN {
            primary_port: None,
            aux_ports: vec![None; n],
        }
    }

    pub(crate) fn name(&self) -> String {
        match self {
            Self::Z4 { .. } => "Z4".to_owned(),
            Self::ZN { aux_ports, .. } => format!("Z{}", aux_ports.len()),
            Self::D { .. } => "D".to_owned(),
            Self::K { .. } => "K".to_owned(),
            Self::S { .. } => "S".to_owned(),
            Self::Var { name, .. } => name.to_owned(),
            Self::Constr { .. } => "Constr".to_owned(),
            Self::Dup { .. } => "Dup".to_owned(),
            Self::Era { .. } => "Era".to_owned(),
        }
    }

    pub(crate) fn set_primary_port(self, primary_port: Option<Port>) -> Self {
        match self {
            Self::Z4 { aux_ports, .. } => Self::Z4 {
                aux_ports,
                primary_port,
            },
            Self::ZN { aux_ports, .. } => Self::ZN {
                aux_ports,
                primary_port,
            },
            Self::D { aux_port, .. } => Self::D {
                primary_port,
                aux_port,
            },
            Self::Constr { aux_ports, .. } => Self::Constr {
                primary_port,
                aux_ports,
            },
            Self::Dup { aux_ports, .. } => Self::Dup {
                primary_port,
                aux_ports,
            },
            Self::Era { .. } => Self::Era { primary_port },
            Self::K { .. } => Self::K { primary_port },
            Self::S { .. } => Self::S { primary_port },
            Self::Var { name, .. } => Self::Var { name, primary_port },
        }
    }

    fn set_aux_port_i(self, i: usize, aux_port: Option<Port>) -> Self {
        match self {
            Self::ZN {
                primary_port,
                mut aux_ports,
            } => {
                aux_ports[i] = aux_port;

                Self::ZN {
                    primary_port,
                    aux_ports,
                }
            }
            Self::Z4 {
                primary_port,
                mut aux_ports,
            } => {
                aux_ports[i] = aux_port;

                Self::Z4 {
                    primary_port,
                    aux_ports,
                }
            }
            e @ Self::Era { .. } => e,
            Self::Constr {
                mut aux_ports,
                primary_port,
            } => {
                aux_ports[i] = aux_port;

                Self::Constr {
                    primary_port,
                    aux_ports,
                }
            }
            Self::Dup {
                mut aux_ports,
                primary_port,
            } => {
                aux_ports[i] = aux_port;

                Self::Dup {
                    primary_port,
                    aux_ports,
                }
            }
            Self::D { primary_port, .. } => {
                assert_eq!(i, 0);

                Self::D {
                    primary_port,
                    aux_port,
                }
            }
            k @ Self::K { .. } => k,
            s @ Self::S { .. } => s,
            v @ Self::Var { .. } => v,
        }
    }

    fn set_port_i(self, i: usize, port: Option<Port>) -> Self {
        if i == 0 {
            self.set_primary_port(port)
        } else {
            self.set_aux_port_i(i - 1, port)
        }
    }

    pub(crate) fn next_empty_port(&self) -> Option<usize> {
        self.iter_ports()
            .enumerate()
            .filter(|(_, x)| x.is_none())
            .map(|(i, _)| i)
            .next()
    }

    pub(crate) fn len_ports(&self) -> usize {
        self.iter_ports().count()
    }

    pub(crate) fn last_empty_port(&self) -> Option<usize> {
        self.iter_ports()
            .enumerate()
            .filter(|(_, x)| x.is_none())
            .map(|(i, _)| i)
            .last()
    }

    fn iter_ports_mut<'a>(&'a mut self) -> Box<dyn Iterator<Item = Option<&'a mut Port>> + 'a> {
        match self {
            Self::ZN {
                primary_port,
                aux_ports,
            } => Box::new(
                [primary_port.as_mut()]
                    .into_iter()
                    .chain(aux_ports.iter_mut().map(|x| x.as_mut())),
            ),
            Self::Z4 {
                primary_port,
                aux_ports,
            } => Box::new(
                [primary_port.as_mut()]
                    .into_iter()
                    .chain(aux_ports.iter_mut().map(|x| x.as_mut())),
            ),
            Self::Constr {
                aux_ports,
                primary_port,
            }
            | Self::Dup {
                aux_ports,
                primary_port,
            } => Box::new(
                [primary_port.as_mut()]
                    .into_iter()
                    .chain(aux_ports.iter_mut().map(|elem| elem.as_mut())),
            ),
            Self::D {
                aux_port,
                primary_port,
            } => Box::new(
                [primary_port.as_mut()]
                    .into_iter()
                    .chain(iter::once(aux_port.as_mut())),
            ),
            Self::Era { primary_port }
            | Self::K { primary_port }
            | Self::S { primary_port }
            | Self::Var { primary_port, .. } => Box::new(iter::once(primary_port.as_mut())),
        }
    }

    pub(crate) fn iter_ports<'a>(&'a self) -> Box<dyn Iterator<Item = Option<&'a Port>> + 'a> {
        match self {
            Self::Z4 {
                primary_port,
                aux_ports,
            } => Box::new(
                [primary_port.as_ref()]
                    .into_iter()
                    .chain(aux_ports.iter().map(|x| x.as_ref())),
            ),
            Self::ZN {
                primary_port,
                aux_ports,
            } => Box::new(
                [primary_port.as_ref()]
                    .into_iter()
                    .chain(aux_ports.iter().map(|x| x.as_ref())),
            ),
            Self::Constr {
                aux_ports,
                primary_port,
            }
            | Self::Dup {
                aux_ports,
                primary_port,
            } => Box::new(
                [primary_port.as_ref()]
                    .into_iter()
                    .chain(aux_ports.iter().map(|elem| elem.as_ref())),
            ),
            Self::D {
                aux_port,
                primary_port,
            } => Box::new(
                [primary_port.as_ref()]
                    .into_iter()
                    .chain(iter::once(aux_port.as_ref())),
            ),
            Self::Era { primary_port }
            | Self::K { primary_port }
            | Self::S { primary_port }
            | Self::Var { primary_port, .. } => Box::new(iter::once(primary_port.as_ref())),
        }
    }

    pub(crate) fn primary_port<'a>(&'a self) -> Option<&'a Port> {
        match self {
            Self::Z4 { primary_port, .. }
            | Self::ZN { primary_port, .. }
            | Self::Constr { primary_port, .. }
            | Self::Dup { primary_port, .. }
            | Self::D { primary_port, .. }
            | Self::Era { primary_port }
            | Self::K { primary_port }
            | Self::S { primary_port }
            | Self::Var { primary_port, .. } => primary_port.as_ref(),
        }
    }

    pub(crate) fn iter_aux_ports<'a>(&'a self) -> Box<dyn Iterator<Item = Option<&'a Port>> + 'a> {
        match self {
            Self::Z4 { aux_ports, .. } => Box::new(aux_ports.iter().map(|elem| elem.as_ref())),
            Self::ZN { aux_ports, .. } => Box::new(aux_ports.iter().map(|elem| elem.as_ref())),
            Self::Constr { aux_ports, .. } | Self::Dup { aux_ports, .. } => {
                Box::new(aux_ports.iter().map(|elem| elem.as_ref()))
            }
            Self::D { aux_port, .. } => Box::new(iter::once(aux_port.as_ref())),
            Self::Era { .. } | Self::K { .. } | Self::S { .. } | Self::Var { .. } => {
                Box::new(iter::empty())
            }
        }
    }

    pub(crate) fn to_named(self, names: &NameIter) -> NamedBuilder {
        NamedBuilder {
            name: names.next_id(),
            builder: self,
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test_log::test]
    fn test_k_comb() {
        let mut names = Default::default();

        let k_comb = OwnedNetBuilder::new(CombinatorBuilder::K { primary_port: None }, &mut names);
        k_comb.expand_step(&mut names).make_root(&mut names);

        k_comb.clone().iter_tree().for_each(|x| println!("{:?}", x));

        let combinated = k_comb.combinate(&mut names).orient();

        println!("{}", combinated);

        assert!(matches!(
            OwnedNetBuilder::decombinate(&combinated).unwrap(),
            SkExpr::K(None, None)
        ));
    }

    #[test_log::test]
    fn test_circular_z() {
        let mut names = NameIter::default();

        let z = OwnedNetBuilder::new(
            CombinatorBuilder::ZN {
                primary_port: None,
                aux_ports: vec![None; 4],
            },
            &mut names,
        );

        OwnedNetBuilder::connect((1, z.clone()), (4, z.clone()));

        let res = z.expand_step(&mut names);

        res.iter_tree().for_each(|x| println!("{:?}", x));
    }

    #[test_log::test]
    fn test_s_comb() {
        let mut names = Default::default();

        let s_comb = OwnedNetBuilder::new(CombinatorBuilder::S { primary_port: None }, &mut names);
        s_comb.expand_step(&mut names).make_root(&mut names);

        let combinated = s_comb.combinate(&mut names).orient();
        let m = OwnedNetBuilder::decombinate(&combinated).unwrap();

        assert!(matches!(m, SkExpr::S(None, None, None)));
    }

    #[test_log::test]
    fn test_k_code() {
        let mut names = Default::default();

        let k_comb = OwnedNetBuilder::new(CombinatorBuilder::K { primary_port: None }, &mut names)
            .encode(&mut names);

        k_comb.expand_step(&mut names);

        let res = k_comb.combinate(&mut names);
    }

    #[test_log::test]
    fn test_decoder() {
        let mut names = Default::default();

        let d_comb = OwnedNetBuilder::new(
            CombinatorBuilder::D {
                primary_port: None,
                aux_port: None,
            },
            &mut names,
        );
        d_comb.expand_step(&mut names);

        let combinated = d_comb.combinate(&mut names);
    }

    #[test_log::test]
    fn test_interaction_net_decoder() {
        use inetlib::reducers::combinators::reduce_dyn;

        let mut names = Default::default();

        let net = OwnedNetBuilder::new(
            CombinatorBuilder::Constr {
                primary_port: None,
                aux_ports: [const { None }; 2],
            },
            &mut names,
        );
        let dup_left = OwnedNetBuilder::new(
            CombinatorBuilder::Dup {
                primary_port: Some((1, net.clone())),
                aux_ports: [const { None }; 2],
            },
            &mut names,
        );
        let dup_right = OwnedNetBuilder::new(
            CombinatorBuilder::Dup {
                primary_port: Some((2, net.clone())),
                aux_ports: [const { None }; 2],
            },
            &mut names,
        );

        OwnedNetBuilder::connect((1, net.clone()), (0, dup_left.clone()));
        OwnedNetBuilder::connect((2, net.clone()), (0, dup_right.clone()));

        let constr = OwnedNetBuilder::new(
            CombinatorBuilder::Constr {
                primary_port: Some((2, dup_right.clone())),
                aux_ports: [None, Some((1, dup_left.clone()))],
            },
            &mut names,
        );
        let constr_parent = OwnedNetBuilder::new(
            CombinatorBuilder::Constr {
                primary_port: Some((1, constr.clone())),
                aux_ports: [Some((1, dup_right.clone())), Some((2, dup_left.clone()))],
            },
            &mut names,
        );

        OwnedNetBuilder::connect((1, constr.clone()), (0, constr_parent.clone()));
        OwnedNetBuilder::connect((2, constr.clone()), (1, dup_left.clone()));

        OwnedNetBuilder::connect((1, dup_left.clone()), (2, constr.clone()));
        OwnedNetBuilder::connect((2, dup_left.clone()), (2, constr_parent.clone()));

        OwnedNetBuilder::connect((1, dup_right.clone()), (1, constr_parent.clone()));
        OwnedNetBuilder::connect((2, dup_right.clone()), (0, constr.clone()));

        let net = net.encode(&mut names);

        net.checksum();

        net.expand_step(&mut names);

        net.checksum();

        let d_comb = OwnedNetBuilder::new(
            CombinatorBuilder::D {
                primary_port: Some((0, net.clone())),
                aux_port: None,
            },
            &mut names,
        );

        OwnedNetBuilder::connect((0, net.clone()), (0, d_comb.clone()));

        d_comb.expand_step(&mut names);

        net.checksum();

        let combinated = net.combinate(&mut names);

        let res = reduce_dyn(&combinated).remove(0);
        res.iter_tree().for_each(|x| println!("{:?}", x));
    }

    #[test_log::test]
    fn test_interaction_code_k_decoder() {
        use inetlib::reducers::combinators::reduce_dyn;

        let mut names = Default::default();

        let coder = OwnedNetBuilder::new(CombinatorBuilder::K { primary_port: None }, &mut names)
            .encode(&mut names);

        coder.clone().iter_tree().for_each(|x| println!("{:?}", x));

        coder.expand_step(&mut names);
        let var = OwnedNetBuilder::new(
            CombinatorBuilder::Var {
                name: "Bruh".to_owned(),
                primary_port: None,
            },
            &mut names,
        );
        let decoder = OwnedNetBuilder::new(
            CombinatorBuilder::D {
                primary_port: None,
                aux_port: Some((0, var.clone())),
            },
            &mut names,
        );

        OwnedNetBuilder::connect((0, var.clone()), (1, decoder.clone()));

        decoder.expand_step(&mut names);

        OwnedNetBuilder::connect((0, coder.clone()), (0, decoder.clone()));

        let comb_coder = coder.combinate(&mut names);
        let _ = decoder.combinate(&mut names);

        let res = reduce_dyn(&comb_coder).remove(0);
        let dec = OwnedNetBuilder::decombinate(&res.orient());

        assert!(matches!(dec, Some(SkExpr::K { .. })))
    }

    #[test_log::test]
    fn test_interaction_code_s_decoder() {
        use inetlib::reducers::combinators::reduce_dyn;

        let mut names = Default::default();

        let coder = OwnedNetBuilder::new(CombinatorBuilder::S { primary_port: None }, &mut names)
            .encode(&mut names);

        coder.expand_step(&mut names);

        let var = OwnedNetBuilder::new(
            CombinatorBuilder::Var {
                name: "Bruh".to_owned(),
                primary_port: None,
            },
            &mut names,
        );
        let decoder = OwnedNetBuilder::new(
            CombinatorBuilder::D {
                primary_port: None,
                aux_port: Some((0, var.clone())),
            },
            &mut names,
        );

        OwnedNetBuilder::connect((0, var.clone()), (1, decoder.clone()));

        decoder.expand_step(&mut names);

        OwnedNetBuilder::connect((0, decoder.clone()), (0, coder.clone()));

        let comb_coder = coder.combinate(&mut names);

        let res = reduce_dyn(&comb_coder).remove(0);
        let dec = OwnedNetBuilder::decombinate(&res.orient());
        matches!(dec, Some(SkExpr::S { .. }));
    }

    #[test_log::test]
    fn test_interaction_manual_z4() {
        use inetlib::reducers::combinators::reduce_dyn;
        use std::collections::BTreeSet;

        let mut names = Default::default();

        let z4_1 = OwnedNetBuilder::new(
            CombinatorBuilder::Z4 {
                primary_port: None,
                aux_ports: [const { None }; 4],
            },
            &mut names,
        );
        let z4_2 = OwnedNetBuilder::new(
            CombinatorBuilder::Z4 {
                primary_port: Some((0, z4_1.clone())),
                aux_ports: [const { None }; 4],
            },
            &mut names,
        );

        OwnedNetBuilder::connect((0, z4_1.clone()), (0, z4_2.clone()));

        let _ = (0..4)
            .enumerate()
            .map(|(i, _)| {
                let v = OwnedNetBuilder::new(
                    CombinatorBuilder::Var {
                        name: names.next_var_name(),
                        primary_port: Some((i + 1, z4_1.clone())),
                    },
                    &mut names,
                );

                OwnedNetBuilder::connect((0, v.clone()), (i + 1, z4_1.clone()));

                v
            })
            .collect::<Vec<_>>();
        let _ = (0..4)
            .enumerate()
            .map(|(i, _)| {
                let v = OwnedNetBuilder::new(
                    CombinatorBuilder::Var {
                        name: names.next_var_name(),
                        primary_port: Some((i + 1, z4_2.clone())),
                    },
                    &mut names,
                );

                OwnedNetBuilder::connect((0, v.clone()), (i + 1, z4_2.clone()));

                v
            })
            .collect::<Vec<_>>();

        z4_1.expand_step(&mut names);
        z4_2.expand_step(&mut names);

        z4_1.clone().iter_tree().for_each(|x| println!("{:?}", x));

        assert_eq!(
            reduce_dyn(&z4_1.combinate(&mut names))
                .into_iter()
                .map(|x| x.to_string())
                .collect::<BTreeSet<_>>(),
            BTreeSet::from_iter([
                "v0 ~ v4".to_owned(),
                "v1 ~ v5".to_owned(),
                "v2 ~ v6".to_owned(),
                "v3 ~ v7".to_owned()
            ])
        );
    }

    #[test_log::test]
    fn test_interaction_z_2() {
        use inetlib::reducers::combinators::reduce_dyn;
        use std::collections::BTreeSet;

        let mut names = Default::default();

        let z2_1 = OwnedNetBuilder::new(
            CombinatorBuilder::ZN {
                primary_port: None,
                aux_ports: vec![None, None],
            },
            &mut names,
        );
        let z2_2 = OwnedNetBuilder::new(
            CombinatorBuilder::ZN {
                primary_port: Some((0, z2_1.clone())),
                aux_ports: vec![None, None],
            },
            &mut names,
        );

        OwnedNetBuilder::connect((0, z2_1.clone()), (0, z2_2.clone()));

        let _ = (0..2)
            .enumerate()
            .map(|(i, _)| {
                let v = OwnedNetBuilder::new(
                    CombinatorBuilder::Var {
                        name: names.next_var_name(),
                        primary_port: Some((i + 1, z2_1.clone())),
                    },
                    &mut names,
                );

                OwnedNetBuilder::connect((1 + i, z2_1.clone()), (0, v.clone()));

                v
            })
            .collect::<Vec<_>>();
        let _ = (0..2)
            .enumerate()
            .map(|(i, _)| {
                let v = OwnedNetBuilder::new(
                    CombinatorBuilder::Var {
                        name: names.next_var_name(),
                        primary_port: Some((i + 1, z2_2.clone())),
                    },
                    &mut names,
                );

                OwnedNetBuilder::connect((1 + i, z2_2.clone()), (0, v.clone()));

                v
            })
            .collect::<Vec<_>>();

        z2_1.expand_step(&mut names);
        z2_2.expand_step(&mut names);

        assert_eq!(
            reduce_dyn(&z2_1.combinate(&mut names))
                .into_iter()
                .map(|x| x.to_string())
                .collect::<BTreeSet<_>>(),
            BTreeSet::from_iter(["v0 ~ v2".to_owned(), "v1 ~ v3".to_owned()])
        );
    }

    #[test_log::test]
    fn test_interaction_z_4() {
        use inetlib::reducers::combinators::reduce_dyn;
        use std::collections::BTreeSet;

        let mut names = Default::default();

        let z4_1 = OwnedNetBuilder::new(
            CombinatorBuilder::ZN {
                primary_port: None,
                aux_ports: vec![None, None, None, None],
            },
            &mut names,
        );
        let z4_2 = OwnedNetBuilder::new(
            CombinatorBuilder::ZN {
                primary_port: Some((0, z4_1.clone())),
                aux_ports: vec![None, None, None, None],
            },
            &mut names,
        );

        OwnedNetBuilder::connect((0, z4_1.clone()), (0, z4_2.clone()));

        let _ = (0..4)
            .enumerate()
            .map(|(i, _)| {
                let v = OwnedNetBuilder::new(
                    CombinatorBuilder::Var {
                        name: names.next_var_name(),
                        primary_port: Some((i + 1, z4_1.clone())),
                    },
                    &mut names,
                );

                OwnedNetBuilder::connect((0, v.clone()), (i + 1, z4_1.clone()));

                v
            })
            .collect::<Vec<_>>();
        let _ = (0..4)
            .enumerate()
            .map(|(i, _)| {
                let v = OwnedNetBuilder::new(
                    CombinatorBuilder::Var {
                        name: names.next_var_name(),
                        primary_port: Some((i + 1, z4_2.clone())),
                    },
                    &mut names,
                );

                OwnedNetBuilder::connect((0, v.clone()), (i + 1, z4_2.clone()));

                v
            })
            .collect::<Vec<_>>();

        z4_1.expand_step(&mut names);
        z4_2.expand_step(&mut names);

        z4_1.clone().iter_tree().for_each(|x| println!("{:?}", x));

        assert_eq!(
            reduce_dyn(&z4_1.combinate(&mut names))
                .into_iter()
                .map(|x| x.to_string())
                .collect::<BTreeSet<_>>(),
            BTreeSet::from_iter([
                "v0 ~ v4".to_owned(),
                "v1 ~ v5".to_owned(),
                "v2 ~ v6".to_owned(),
                "v3 ~ v7".to_owned()
            ])
        );
    }

    #[test_log::test]
    fn test_interaction_z_n() {
        use inetlib::reducers::combinators::reduce_dyn;
        use std::collections::BTreeSet;

        for i in 1..10 {
            let mut names = Default::default();
            let names_b: NameIter = Default::default();

            let zn_1 = OwnedNetBuilder::new(
                CombinatorBuilder::ZN {
                    primary_port: None,
                    aux_ports: vec![None; i],
                },
                &mut names,
            );
            let zn_2 = OwnedNetBuilder::new(
                CombinatorBuilder::ZN {
                    primary_port: None,
                    aux_ports: vec![None; i],
                },
                &mut names,
            );

            OwnedNetBuilder::connect((0, zn_1.clone()), (0, zn_2.clone()));

            let _ = (0..i)
                .enumerate()
                .map(|(i, _)| {
                    let v = OwnedNetBuilder::new(
                        CombinatorBuilder::Var {
                            name: names.next_var_name(),
                            primary_port: Some((i + 1, zn_1.clone())),
                        },
                        &mut names,
                    );

                    OwnedNetBuilder::connect((0, v.clone()), (i + 1, zn_1.clone()));

                    v
                })
                .collect::<Vec<_>>();
            let _ = (0..i)
                .enumerate()
                .map(|(i, _)| {
                    let v = OwnedNetBuilder::new(
                        CombinatorBuilder::Var {
                            name: format!("_{}", names_b.next_var_name()),
                            primary_port: Some((i + 1, zn_2.clone())),
                        },
                        &mut names,
                    );

                    OwnedNetBuilder::connect((0, v.clone()), (1 + i, zn_2.clone()));

                    v
                })
                .collect::<Vec<_>>();

            let zn_1 = zn_1.expand_step(&mut names);
            let _ = zn_2.expand_step(&mut names);

            let results = reduce_dyn(&zn_1.combinate(&mut names));

            if i == 1 {
                assert_eq!(&results[0].to_string(), "v0 ~ _v0");

                continue;
            }

            assert_eq!(
                results
                    .into_iter()
                    .map(|x| x.to_string())
                    .collect::<BTreeSet<_>>(),
                (0..i)
                    .map(|j| { format!("v{} ~ _v{}", j, j) })
                    .collect::<BTreeSet<_>>()
            );
        }
    }
}
