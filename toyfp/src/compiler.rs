use super::{parser::Expr, parser_sk::Expr as SkExpr};
use inetlib::parser::{ast_combinators::Port as AstPort, naming::NameIter};
use std::{cell::RefCell, iter, rc::Rc};

type Port = (usize, OwnedNetBuilder);

#[derive(Debug, Clone)]
struct OwnedNetBuilder(Rc<RefCell<NamedBuilder>>);

impl OwnedNetBuilder {
    fn new(b: CombinatorBuilder, names: &mut NameIter) -> Self {
        Self(Rc::new(RefCell::new(b.to_named(names))))
    }
}

impl OwnedNetBuilder {
    fn update_with(&self, mut f: impl FnMut(&CombinatorBuilder) -> CombinatorBuilder) -> &Self {
        self.0.replace_with(|val| {
            let mut new_val = val.clone();

            let new_builder = f(&val.builder);
            new_val.builder = new_builder;

            new_val
        });

        self
    }

    pub(crate) fn expand_step(&self, names: &mut NameIter) -> &Self {
        self.update_with(|builder| match &builder {
            CombinatorBuilder::Z3 {
                primary_port,
                aux_ports,
            } => {
                let parent_constr = OwnedNetBuilder::new(
                    CombinatorBuilder::Constr {
                        aux_ports: [aux_ports[0].clone(), aux_ports[1].clone()],
                        primary_port: None,
                    },
                    names,
                );
                let child_constr = CombinatorBuilder::Constr {
                    aux_ports: [Some((0, parent_constr.clone())), aux_ports[2].clone()],
                    primary_port: primary_port.clone(),
                };
                let child_constr_ref = self;

                // Parent <-> child
                parent_constr.update_with(|builder| {
                    builder
                        .clone()
                        .with_primary_port(Some((1, child_constr_ref.clone())))
                });

                // Primary port <-> child
                if let Some((port, p)) = primary_port {
                    p.update_with(|builder| {
                        builder
                            .clone()
                            .with_port_i(*port, Some((2, child_constr_ref.clone())))
                    });
                }

                // aux rightmost <-> child
                if let Some((port, aux)) = &aux_ports[2] {
                    aux.update_with(|builder| {
                        builder
                            .clone()
                            .with_port_i(*port, Some((2, child_constr_ref.clone())))
                    });
                }

                // aux middle <-> parent
                if let Some((port, aux)) = &aux_ports[1] {
                    aux.update_with(|builder| {
                        builder
                            .clone()
                            .with_port_i(*port, Some((2, parent_constr.clone())))
                    });
                }

                // aux left <-> parent
                if let Some((port, aux)) = &aux_ports[0] {
                    aux.update_with(|builder| {
                        builder
                            .clone()
                            .with_port_i(*port, Some((1, parent_constr.clone())))
                    });
                }

                child_constr
            }
            CombinatorBuilder::Z4 {
                primary_port,
                aux_ports,
            } => {
                let top_constr = OwnedNetBuilder::new(
                    CombinatorBuilder::Constr {
                        aux_ports: [aux_ports[0].clone(), aux_ports[1].clone()],
                        primary_port: None,
                    },
                    names,
                );
                let parent_constr = OwnedNetBuilder::new(
                    CombinatorBuilder::Constr {
                        aux_ports: [Some((0, top_constr.clone())), aux_ports[2].clone()],
                        primary_port: None,
                    },
                    names,
                );
                let child_constr = CombinatorBuilder::Constr {
                    aux_ports: [Some((0, parent_constr.clone())), aux_ports[3].clone()],
                    primary_port: primary_port.clone(),
                };
                let child_constr_ref = self;

                // Parent <-> child
                parent_constr.update_with(|builder| {
                    builder
                        .clone()
                        .with_primary_port(Some((1, child_constr_ref.clone())))
                });
                top_constr.update_with(|builder| {
                    builder
                        .clone()
                        .with_primary_port(Some((1, parent_constr.clone())))
                });

                // Primary port <-> child
                if let Some((port, p)) = primary_port {
                    p.update_with(|builder| {
                        builder
                            .clone()
                            .with_port_i(*port, Some((2, child_constr_ref.clone())))
                    });
                }

                if let Some((port, aux)) = &aux_ports[0] {
                    aux.update_with(|builder| {
                        builder
                            .clone()
                            .with_port_i(*port, Some((1, top_constr.clone())))
                    });
                }

                // aux left <-> parent
                if let Some((port, aux)) = &aux_ports[1] {
                    aux.update_with(|builder| {
                        builder
                            .clone()
                            .with_port_i(*port, Some((2, top_constr.clone())))
                    });
                }

                // aux rightmost <-> child
                if let Some((port, aux)) = &aux_ports[2] {
                    aux.update_with(|builder| {
                        builder
                            .clone()
                            .with_port_i(*port, Some((2, parent_constr.clone())))
                    });
                }

                // aux middle <-> parent
                if let Some((port, aux)) = &aux_ports[3] {
                    aux.update_with(|builder| {
                        builder
                            .clone()
                            .with_port_i(*port, Some((2, child_constr_ref.clone())))
                    });
                }

                child_constr
            }
            CombinatorBuilder::D {
                ref primary_port,
                aux_port,
            } => {
                let dup = OwnedNetBuilder::new(
                    CombinatorBuilder::Dup {
                        primary_port: None,
                        aux_ports: [const { None }; 2],
                    },
                    names,
                );
                let root = CombinatorBuilder::Z4 {
                    primary_port: primary_port.clone(),
                    aux_ports: [
                        Some((1, dup.clone())),
                        Some((2, dup.clone())),
                        Some((0, dup.clone())),
                        aux_port.clone(),
                    ],
                };
                let root_ref = self;

                // Aux <-> root
                if let Some((port, aux)) = aux_port {
                    aux.update_with(|builder| {
                        builder
                            .clone()
                            .with_port_i(*port, Some((4, root_ref.clone())))
                    });
                }

                // Dup <-> root
                dup.update_with(|builder| {
                    builder
                        .clone()
                        .with_primary_port(Some((3, root_ref.clone())))
                        .with_aux_port_i(0, Some((2, root_ref.clone())))
                        .with_aux_port_i(1, Some((1, root_ref.clone())))
                });

                root
            }
            CombinatorBuilder::K { primary_port } => {
                let d = OwnedNetBuilder::new(
                    CombinatorBuilder::D {
                        primary_port: None,
                        aux_port: None,
                    },
                    names,
                );
                let e = OwnedNetBuilder::new(CombinatorBuilder::Era { primary_port: None }, names);
                let root = CombinatorBuilder::Z3 {
                    primary_port: primary_port.clone(),
                    aux_ports: [
                        Some((1, d.clone())),
                        Some((0, e.clone())),
                        Some((0, d.clone())),
                    ],
                };
                let root_ref = self;

                d.update_with(|builder| {
                    builder
                        .clone()
                        .with_primary_port(Some((3, root_ref.clone())))
                        .with_aux_port_i(0, Some((1, root_ref.clone())))
                });
                e.update_with(|builder| {
                    builder
                        .clone()
                        .with_primary_port(Some((2, root_ref.clone())))
                });

                // primary port <-> Z
                if let Some((port, p)) = primary_port {
                    p.update_with(|builder| {
                        builder
                            .clone()
                            .with_port_i(*port, Some((0, root_ref.clone())))
                    });
                }

                root
            }
            CombinatorBuilder::S { primary_port } => {
                let top_left_z = OwnedNetBuilder::new(
                    CombinatorBuilder::Z4 {
                        primary_port: primary_port.clone(),
                        aux_ports: [const { None }; 4],
                    },
                    names,
                );
                let middle_left_z = OwnedNetBuilder::new(
                    CombinatorBuilder::Z4 {
                        primary_port: None,
                        aux_ports: [const { None }; 4],
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
                let right_bottom_z = CombinatorBuilder::Z4 {
                    primary_port: primary_port.clone(),
                    aux_ports: [
                        Some((2, bottom_middle_right_constr.clone())),
                        Some((0, dup.clone())),
                        Some((0, top_left_z.clone())),
                        Some((0, d.clone())),
                    ],
                };

                right_bottom_z
                    .iter_aux_ports()
                    .enumerate()
                    .filter_map(|(i, x)| Some((i, x?)))
                    .for_each(|(i, (port, p))| {
                        (*p).update_with(|builder| {
                            builder
                                .clone()
                                .with_port_i(*port, Some((1 + i, right_bottom_z_ref.clone())))
                        });
                    });

                // Connect dup to constrs
                dup.update_with(|builder| {
                    builder
                        .clone()
                        .with_push_aux_port(Some((2, left_middle_constr.clone())))
                        .with_push_aux_port(Some((2, middle_constr.clone())))
                });

                // Connect bottom right constr to top right constr, Z
                bottom_middle_right_constr.update_with(|builder| {
                    builder
                        .clone()
                        .with_aux_port_i(2, Some((0, middle_left_z.clone())))
                        .with_primary_port(Some((1, middle_constr.clone())))
                });

                middle_constr.update_with(|builder| {
                    builder
                        .clone()
                        .with_primary_port(Some((1, d.clone())))
                        .with_push_aux_port(Some((0, bottom_middle_right_constr.clone())))
                        .with_push_aux_port(Some((2, dup.clone())))
                });
                d.update_with(|builder| {
                    builder
                        .clone()
                        .with_push_aux_port(Some((0, middle_constr.clone())))
                });

                left_middle_constr.update_with(|builder| {
                    builder
                        .clone()
                        .with_primary_port(Some((1, middle_left_z.clone())))
                        .with_push_aux_port(Some((4, middle_left_z.clone())))
                        .with_push_aux_port(Some((1, dup.clone())))
                });

                top_left_z.update_with(|builder| {
                    builder
                        .clone()
                        .with_primary_port(Some((3, right_bottom_z_ref.clone())))
                        .with_aux_port_i(3, Some((1, top_left_z.clone())))
                        .with_aux_port_i(2, Some((3, middle_left_z.clone())))
                        .with_aux_port_i(1, Some((2, middle_left_z.clone())))
                        .with_aux_port_i(0, Some((4, top_left_z.clone())))
                });

                right_bottom_z
            }
            e @ CombinatorBuilder::Var { .. }
            | e @ CombinatorBuilder::Constr { .. }
            | e @ CombinatorBuilder::Era { .. }
            | e @ CombinatorBuilder::Dup { .. } => (*e).clone(),
        })
    }
}

#[derive(Debug, Clone)]
struct NamedBuilder {
    name: usize,
    builder: CombinatorBuilder,
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

#[derive(Debug, Clone)]
enum CombinatorBuilder {
    Z4 {
        primary_port: Option<Port>,
        aux_ports: [Option<Port>; 4],
    },
    Z3 {
        primary_port: Option<Port>,
        aux_ports: [Option<Port>; 3],
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
        name: usize,
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

impl CombinatorBuilder {
    fn with_primary_port(self, primary_port: Option<Port>) -> Self {
        match self {
            Self::Z3 { aux_ports, .. } => Self::Z3 {
                aux_ports,
                primary_port,
            },
            Self::Z4 { aux_ports, .. } => Self::Z4 {
                primary_port,
                aux_ports,
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

    fn with_aux_port_i(self, i: usize, aux_port: Option<Port>) -> Self {
        match self {
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
            Self::Z4 {
                mut aux_ports,
                primary_port,
            } => {
                aux_ports[i] = aux_port;

                Self::Z4 {
                    primary_port,
                    aux_ports,
                }
            }
            Self::Z3 {
                mut aux_ports,
                primary_port,
            } => {
                aux_ports[i] = aux_port;

                Self::Z3 {
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

    fn with_port_i(self, i: usize, port: Option<Port>) -> Self {
        if i == 0 {
            self.with_primary_port(port)
        } else {
            self.with_aux_port_i(1 + i, port)
        }
    }

    fn set_ports(self, mut ports: impl Iterator<Item = Option<Port>>) -> Self {
        let primary_port = ports.next();

        let slf = self.with_primary_port(primary_port.flatten());

        ports
            .enumerate()
            .fold(slf, |acc, (i, x)| acc.with_aux_port_i(i, x))
    }

    fn iter_ports<'a>(&'a self) -> Box<dyn Iterator<Item = Option<&'a Port>> + 'a> {
        match self {
            Self::Z3 {
                aux_ports,
                primary_port,
            } => Box::new(
                [primary_port.as_ref()]
                    .into_iter()
                    .chain(aux_ports.iter().map(|elem| elem.as_ref())),
            ),
            Self::Z4 {
                aux_ports,
                primary_port,
            } => Box::new(
                [primary_port.as_ref()]
                    .into_iter()
                    .chain(aux_ports.iter().map(|elem| elem.as_ref())),
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

    fn primary_port(&self) -> Option<&Port> {
        match self {
            Self::Constr { primary_port, .. }
            | Self::Era { primary_port, .. }
            | Self::Dup { primary_port, .. }
            | Self::D { primary_port, .. }
            | Self::Z3 { primary_port, .. }
            | Self::Z4 { primary_port, .. }
            | Self::K { primary_port, .. }
            | Self::S { primary_port, .. }
            | Self::Var { primary_port, .. } => primary_port.as_ref(),
        }
    }

    fn iter_aux_ports<'a>(&'a self) -> Box<dyn Iterator<Item = Option<&'a Port>> + 'a> {
        match self {
            Self::Z3 { aux_ports, .. } => Box::new(aux_ports.iter().map(|elem| elem.as_ref())),
            Self::Z4 { aux_ports, .. } => Box::new(aux_ports.iter().map(|elem| elem.as_ref())),
            Self::Constr { aux_ports, .. } | Self::Dup { aux_ports, .. } => {
                Box::new(aux_ports.iter().map(|elem| elem.as_ref()))
            }
            Self::D { aux_port, .. } => Box::new(iter::once(aux_port.as_ref())),
            Self::Era { .. } | Self::K { .. } | Self::S { .. } | Self::Var { .. } => {
                Box::new(iter::empty())
            }
        }
    }

    fn with_push_aux_port(self, aux_port: Option<Port>) -> Self {
        let first_empty_slot = self.iter_aux_ports().position(|elem| elem.is_none());

        if let Some(pos) = first_empty_slot {
            self.with_aux_port_i(pos, aux_port)
        } else {
            self
        }
    }

    fn to_named(self, names: &mut NameIter) -> NamedBuilder {
        NamedBuilder {
            name: names.next_id(),
            builder: self,
        }
    }
}

pub fn compile_sk(e: SkExpr, names: &mut NameIter) -> Port {
    todo!()
}

pub fn compile(e: Expr, names: &mut NameIter) -> AstPort {
    todo!()
}

pub fn decompile(p: &Port) -> Option<Expr> {
    todo!()
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_make_z_comb() {
        let cases = [
            (0, "Era[@0](v0)"),
            (1, "v0 ~ v1"),
            (2, "Constr[@0](v3, v0, v2)"),
            (3, "Constr[@3](v5, Constr[@0](@3, v0, v2), v4)"),
            (
                4,
                "Constr[@6](v7, Constr[@3](@6, Constr[@0](@3, v0, v2), v4), v6)",
            ),
        ];

        for (case, expected) in cases {
            assert_eq!(
                make_z_comb(case, &mut NameIter::default()).to_string(),
                expected
            );
        }
    }

    #[test]
    fn test_make_d_comb() {
        assert_eq!(
            make_d_comb(&mut NameIter::default()).to_string(),
            "Constr[@6](v7, Constr[@3](@6, Constr[@0](@3, Dup[@9](@3, @0, @0), @9), @9), v6)"
        );
    }

    #[test]
    fn test_make_k_comb() {
        assert_eq!(
            make_k_comb(&mut NameIter::default()).to_string(),
            "Constr[@3](v5, Constr[@0](@3, Constr[@12](@3, Constr[@9](@12, Constr[@6](@9, Dup[@15](@9, @6, @6), @15), @15), @0), Era[@16](@0)), @12)"
        );
    }
}
