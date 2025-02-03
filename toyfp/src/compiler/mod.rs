use super::{parser::Expr, parser_sk::Expr as SkExpr};
use builder::{CombinatorBuilder as SkCombinatorBuilder, OwnedNetBuilder};
use inetlib::parser::{ast_combinators::Port as AstPort, naming::NameIter};
use std::collections::BTreeMap;

mod builder;
mod icalc;

pub trait CombinatorBuilder: Sized {
    type CPort;
    type EExpr;

    fn decombinate(p: &Self::CPort) -> Option<Self::EExpr>;

    fn combinate(
        &self,
        built: &mut BTreeMap<usize, Self::CPort>,
        names: &mut NameIter,
    ) -> Self::CPort;

    fn expand_step(&self, names: &mut NameIter) -> &Self;
}

pub fn compile_sk(e: SkExpr) -> AstPort {
    let mut names = NameIter::default();

    let cc = build_compilation_expr(e, &mut names);

    cc.combinate(&mut Default::default(), &mut names)
}

pub fn decode_sk(p: &AstPort) -> SkExpr {
    OwnedNetBuilder::decombinate(p).expect("invalid SK expression")
}

fn build_arg_compilation_expr(e: SkExpr, names: &mut NameIter) -> OwnedNetBuilder {
    match e {
        SkExpr::Var(v) => OwnedNetBuilder::new(
            SkCombinatorBuilder::Code(Box::new(SkCombinatorBuilder::Var {
                name: v,
                primary_port: None,
            })),
            names,
        ),
        SkExpr::K(a, b) => {
            let e = OwnedNetBuilder::new(
                SkCombinatorBuilder::Code(Box::new(SkCombinatorBuilder::K { primary_port: None })),
                names,
            );

            let a_cc = a.map(|a| build_arg_compilation_expr(*a, names));
            let b_cc = b.map(|b| build_arg_compilation_expr(*b, names));

            if let Some(a_port) = a_cc.map(|a| (0, a)) {
                let empty_port_var = OwnedNetBuilder::new(
                    SkCombinatorBuilder::Var {
                        name: names.next(),
                        primary_port: None,
                    },
                    names,
                );
                let e_parent = OwnedNetBuilder::new(
                    SkCombinatorBuilder::Constr {
                        primary_port: Some((0, e.clone())),
                        aux_ports: [Some((0, empty_port_var.clone())), Some(a_port.clone())],
                    },
                    names,
                );
                empty_port_var.update_with(|builder| {
                    builder
                        .clone()
                        .with_primary_port(Some((1, e_parent.clone())))
                });

                a_port.1.update_with(|builder| {
                    builder
                        .clone()
                        .with_primary_port(Some((2, e_parent.clone())))
                });

                if let Some(b_port) = b_cc.map(|b| (0, b)) {
                    let empty_port_var = OwnedNetBuilder::new(
                        SkCombinatorBuilder::Var {
                            name: names.next(),
                            primary_port: None,
                        },
                        names,
                    );
                    let constr_parent = OwnedNetBuilder::new(
                        SkCombinatorBuilder::Constr {
                            primary_port: Some((1, e_parent.clone())),
                            aux_ports: [Some((0, empty_port_var.clone())), Some(b_port.clone())],
                        },
                        names,
                    );

                    empty_port_var.update_with(|builder| {
                        builder
                            .clone()
                            .with_primary_port(Some((1, constr_parent.clone())))
                    });

                    b_port.1.update_with(|builder| {
                        builder
                            .clone()
                            .with_primary_port(Some((2, constr_parent.clone())))
                    });

                    e_parent.update_with(|builder| {
                        builder
                            .clone()
                            .with_push_aux_port(Some((0, constr_parent.clone())))
                    });
                }

                e.update_with(|builder| {
                    builder
                        .clone()
                        .with_primary_port(Some((0, e_parent.clone())))
                });
            };

            e.expand_step(names);

            e
        }
        SkExpr::S(a, b, c) => {
            let e = OwnedNetBuilder::new(
                SkCombinatorBuilder::Code(Box::new(SkCombinatorBuilder::S { primary_port: None })),
                names,
            );

            let a_cc = a.map(|a| build_arg_compilation_expr(*a, names));
            let b_cc = b.map(|b| build_arg_compilation_expr(*b, names));
            let c_cc = c.map(|c| build_arg_compilation_expr(*c, names));

            if let Some(a_port) = a_cc.map(|a| (0, a)) {
                let empty_port_var = OwnedNetBuilder::new(
                    SkCombinatorBuilder::Var {
                        name: names.next_var_name(),
                        primary_port: None,
                    },
                    names,
                );
                let e_parent = OwnedNetBuilder::new(
                    SkCombinatorBuilder::Constr {
                        primary_port: None,
                        aux_ports: [Some((0, empty_port_var.clone())), Some(a_port)],
                    },
                    names,
                );
                empty_port_var.update_with(|builder| {
                    builder
                        .clone()
                        .with_primary_port(Some((1, e_parent.clone())))
                });

                if let Some(b_port) = b_cc.map(|b| (0, b)) {
                    let empty_port_var = OwnedNetBuilder::new(
                        SkCombinatorBuilder::Var {
                            name: names.next_var_name(),
                            primary_port: None,
                        },
                        names,
                    );
                    let constr_parent = OwnedNetBuilder::new(
                        SkCombinatorBuilder::Constr {
                            primary_port: Some((0, e.clone())),
                            aux_ports: [Some((0, empty_port_var.clone())), Some(b_port)],
                        },
                        names,
                    );

                    e_parent.update_with(|builder| {
                        builder
                            .clone()
                            .with_push_aux_port(Some((0, constr_parent.clone())))
                    });
                    empty_port_var.update_with(|builder| {
                        builder
                            .clone()
                            .with_primary_port(Some((1, constr_parent.clone())))
                    });

                    if let Some(c_port) = c_cc.map(|c| (0, c)) {
                        let constr_parent_parent = OwnedNetBuilder::new(
                            SkCombinatorBuilder::Constr {
                                primary_port: Some((0, constr_parent.clone())),
                                aux_ports: [None, Some(c_port)],
                            },
                            names,
                        );

                        constr_parent.update_with(|builder| {
                            builder
                                .clone()
                                .with_push_aux_port(Some((0, constr_parent_parent.clone())))
                        });
                    }
                }

                e.update_with(|builder| {
                    builder
                        .clone()
                        .with_primary_port(Some((0, e_parent.clone())))
                });
            };

            e.expand_step(names);

            e
        }
    }
}

fn build_compilation_expr(e: SkExpr, names: &mut NameIter) -> OwnedNetBuilder {
    match e {
        SkExpr::Var(v) => OwnedNetBuilder::new(
            SkCombinatorBuilder::Var {
                name: v,
                primary_port: None,
            },
            names,
        ),
        SkExpr::K(a, b) => {
            let e = OwnedNetBuilder::new(SkCombinatorBuilder::K { primary_port: None }, names);

            let a_cc = a.map(|a| build_arg_compilation_expr(*a, names));
            let b_cc = b.map(|b| build_arg_compilation_expr(*b, names));

            if let Some(a_port) = a_cc.map(|a| (0, a)) {
                let empty_port_var = OwnedNetBuilder::new(
                    SkCombinatorBuilder::Var {
                        name: names.next(),
                        primary_port: None,
                    },
                    names,
                );
                let e_parent = OwnedNetBuilder::new(
                    SkCombinatorBuilder::Constr {
                        primary_port: Some((0, e.clone())),
                        aux_ports: [Some((0, empty_port_var.clone())), Some(a_port.clone())],
                    },
                    names,
                );
                empty_port_var.update_with(|builder| {
                    builder
                        .clone()
                        .with_primary_port(Some((1, e_parent.clone())))
                });

                a_port.1.update_with(|builder| {
                    builder
                        .clone()
                        .with_primary_port(Some((2, e_parent.clone())))
                });

                if let Some(b_port) = b_cc.map(|b| (0, b)) {
                    let empty_port_var = OwnedNetBuilder::new(
                        SkCombinatorBuilder::Var {
                            name: names.next(),
                            primary_port: None,
                        },
                        names,
                    );
                    let constr_parent = OwnedNetBuilder::new(
                        SkCombinatorBuilder::Constr {
                            primary_port: Some((1, e_parent.clone())),
                            aux_ports: [Some((0, empty_port_var.clone())), Some(b_port.clone())],
                        },
                        names,
                    );

                    empty_port_var.update_with(|builder| {
                        builder
                            .clone()
                            .with_primary_port(Some((1, constr_parent.clone())))
                    });

                    b_port.1.update_with(|builder| {
                        builder
                            .clone()
                            .with_primary_port(Some((2, constr_parent.clone())))
                    });

                    e_parent.update_with(|builder| {
                        builder
                            .clone()
                            .with_push_aux_port(Some((0, constr_parent.clone())))
                    });
                }

                e.update_with(|builder| {
                    builder
                        .clone()
                        .with_primary_port(Some((0, e_parent.clone())))
                });
            };

            e.expand_step(names);

            e
        }
        SkExpr::S(a, b, c) => {
            let e = OwnedNetBuilder::new(SkCombinatorBuilder::S { primary_port: None }, names);

            let a_cc = a.map(|a| build_arg_compilation_expr(*a, names));
            let b_cc = b.map(|b| build_arg_compilation_expr(*b, names));
            let c_cc = c.map(|c| build_arg_compilation_expr(*c, names));

            if let Some(a_port) = a_cc.map(|a| (0, a)) {
                let empty_port_var = OwnedNetBuilder::new(
                    SkCombinatorBuilder::Var {
                        name: names.next_var_name(),
                        primary_port: None,
                    },
                    names,
                );
                let e_parent = OwnedNetBuilder::new(
                    SkCombinatorBuilder::Constr {
                        primary_port: None,
                        aux_ports: [Some((0, empty_port_var.clone())), Some(a_port)],
                    },
                    names,
                );
                empty_port_var.update_with(|builder| {
                    builder
                        .clone()
                        .with_primary_port(Some((1, e_parent.clone())))
                });

                if let Some(b_port) = b_cc.map(|b| (0, b)) {
                    let empty_port_var = OwnedNetBuilder::new(
                        SkCombinatorBuilder::Var {
                            name: names.next_var_name(),
                            primary_port: None,
                        },
                        names,
                    );
                    let constr_parent = OwnedNetBuilder::new(
                        SkCombinatorBuilder::Constr {
                            primary_port: Some((0, e.clone())),
                            aux_ports: [Some((0, empty_port_var.clone())), Some(b_port)],
                        },
                        names,
                    );

                    e_parent.update_with(|builder| {
                        builder
                            .clone()
                            .with_push_aux_port(Some((0, constr_parent.clone())))
                    });
                    empty_port_var.update_with(|builder| {
                        builder
                            .clone()
                            .with_primary_port(Some((1, constr_parent.clone())))
                    });

                    if let Some(c_port) = c_cc.map(|c| (0, c)) {
                        let constr_parent_parent = OwnedNetBuilder::new(
                            SkCombinatorBuilder::Constr {
                                primary_port: Some((0, constr_parent.clone())),
                                aux_ports: [None, Some(c_port)],
                            },
                            names,
                        );

                        constr_parent.update_with(|builder| {
                            builder
                                .clone()
                                .with_push_aux_port(Some((0, constr_parent_parent.clone())))
                        });
                    }
                }

                e.update_with(|builder| {
                    builder
                        .clone()
                        .with_primary_port(Some((0, e_parent.clone())))
                });
            };

            e.expand_step(names);

            e
        }
    }
}

pub fn compile(e: Expr, names: &mut NameIter) -> AstPort {
    todo!()
}

pub fn decompile(p: &AstPort) -> Option<Expr> {
    todo!()
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::parser_sk::{lexer, parser};
    use chumsky::Parser;

    #[test_log::test]
    fn test_eval_k() {
        let cases = [("(K)", "(K)"), ("(K(K)(K))", "(K)")];

        for (case, expected) in cases {
            let parsed = parser().parse(lexer().parse(case).unwrap()).unwrap();

            assert_eq!(decode_sk(&compile_sk(parsed.into())).to_string(), expected);
        }
    }
}
