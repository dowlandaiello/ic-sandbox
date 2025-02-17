use super::{
    parser::Expr,
    parser_icalc::{
        self, Abstraction, Application, Duplication, Expr as IExpr, Stmt as IStmt, Superposition,
        Var as IVar,
    },
    parser_sk::Expr as SkExpr,
};
use builder::{CombinatorBuilder as SkCombinatorBuilder, OwnedNetBuilder};
use inetlib::parser::{
    ast_combinators::{Constructor, Duplicator, Expr as CExpr, Port as AstPort, Var},
    ast_lafont::Ident,
    naming::NameIter,
};
use std::collections::BTreeMap;

mod builder;
mod icalc;

pub trait CombinatorBuilder: Sized {
    type CPort;
    type EExpr;

    fn decombinate(p: &Self::CPort) -> Option<Self::EExpr>;

    fn combinate(&self, names: &mut NameIter) -> Self::CPort;

    fn expand_step(&self, names: &mut NameIter) -> Self;
}

pub fn decompile_icalc(p: AstPort) -> IExpr {
    todo!()
}

pub fn compile_icalc(s: Vec<IStmt>) -> Vec<AstPort> {
    fn cc_expr(
        e: IExpr,
        net: &mut Vec<AstPort>,
        tags: &mut BTreeMap<String, Vec<usize>>,
        names: &mut NameIter,
    ) -> AstPort {
        tracing::trace!("compiling {:?}", e);

        match e {
            IExpr::Abstraction(Abstraction { bind_var, body }) => {
                let body_cc = cc_expr(*body, net, tags, names);
                let var_cc = CExpr::Var(Var {
                    name: Ident(bind_var.to_string()),
                    port: None,
                })
                .into_port(names);

                let lam = CExpr::Constr(Constructor {
                    primary_port: None,
                    aux_ports: [Some((0, body_cc.clone())), Some((0, var_cc.clone()))],
                })
                .into_port(names);

                var_cc.borrow_mut().set_primary_port(Some((2, lam.clone())));
                body_cc
                    .borrow_mut()
                    .set_primary_port(Some((1, lam.clone())));

                lam
            }
            IExpr::Application(Application(lhs, rhs)) => {
                let lhs_cc = cc_expr(*lhs, net, tags, names);
                let rhs_cc = cc_expr(*rhs, net, tags, names);

                let ret_var = CExpr::Var(Var {
                    name: Ident("ret".into()),
                    port: None,
                })
                .into_port(names);

                let app = CExpr::Constr(Constructor {
                    primary_port: Some((0, lhs_cc.clone())),
                    aux_ports: [Some((0, ret_var.clone())), Some((0, rhs_cc.clone()))],
                })
                .into_port(names);

                ret_var
                    .borrow_mut()
                    .set_primary_port(Some((1, app.clone())));
                rhs_cc.borrow_mut().set_primary_port(Some((2, app.clone())));

                lhs_cc.borrow_mut().set_primary_port(Some((0, app.clone())));

                println!("{}", lhs_cc);

                net.push(lhs_cc.clone());

                lhs_cc
            }
            IExpr::Duplication(Duplication {
                pair: (a, b),
                to_clone,
                in_expr,
                tag,
            }) => {
                let a_cc = CExpr::Var(Var {
                    name: Ident(a),
                    port: None,
                })
                .into_port(names);
                let b_cc = CExpr::Var(Var {
                    name: Ident(b),
                    port: None,
                })
                .into_port(names);
                let let_cc = CExpr::Dup(Duplicator {
                    primary_port: None,
                    aux_ports: [Some((0, b_cc.clone())), Some((0, a_cc.clone()))],
                })
                .into_port(names);

                cc_expr(*in_expr, net, tags, names);

                tags.entry(tag).or_default().push(let_cc.id);

                a_cc.borrow_mut()
                    .set_primary_port(Some((2, let_cc.clone())));
                a_cc.borrow_mut()
                    .set_primary_port(Some((2, let_cc.clone())));

                let pair_cc = cc_expr(*to_clone, net, tags, names);

                pair_cc
                    .borrow_mut()
                    .set_primary_port(Some((0, let_cc.clone())));
                let_cc
                    .borrow_mut()
                    .set_primary_port(Some((0, pair_cc.clone())));

                println!("{}", pair_cc);

                net.push(pair_cc);

                let_cc
            }
            IExpr::Superposition(Superposition { tag, lhs, rhs }) => {
                let lhs_cc = cc_expr(*lhs, net, tags, names);
                let rhs_cc = cc_expr(*rhs, net, tags, names);

                let pair_cc = CExpr::Dup(Duplicator {
                    primary_port: None,
                    aux_ports: [Some((0, lhs_cc.clone())), Some((0, rhs_cc.clone()))],
                })
                .into_port(names);

                lhs_cc
                    .borrow_mut()
                    .set_primary_port(Some((1, pair_cc.clone())));
                rhs_cc
                    .borrow_mut()
                    .set_primary_port(Some((2, pair_cc.clone())));

                tags.entry(tag).or_default().push(pair_cc.id);

                pair_cc
            }
            IExpr::Variable(IVar(i)) => CExpr::Var(Var {
                name: Ident(i),
                port: None,
            })
            .into_port(names),
        }
    }

    let mut names = Default::default();
    let mut net = Default::default();
    let mut tags = Default::default();

    let def_table = s
        .iter()
        .filter_map(|stmt| match stmt {
            IStmt::Def(d) => Some((d.name.clone(), d.definition.clone())),
            _ => None,
        })
        .collect::<BTreeMap<_, _>>();

    let expr = if let Some(root) = s
        .into_iter()
        .filter_map(|stmt| match stmt {
            IStmt::Expr(e) => Some(e),
            _ => None,
        })
        .next()
    {
        root
    } else {
        return Default::default();
    };

    fn inline(e: IExpr, def_table: &BTreeMap<String, IExpr>) -> IExpr {
        match e {
            IExpr::Abstraction(Abstraction { bind_var, body }) => IExpr::Abstraction(Abstraction {
                bind_var,
                body: Box::new(inline(*body, def_table)),
            }),
            IExpr::Application(Application(lhs, rhs)) => IExpr::Application(Application(
                Box::new(inline(*lhs, def_table)),
                Box::new(inline(*rhs, def_table)),
            )),
            IExpr::Duplication(Duplication {
                tag,
                pair,
                to_clone,
                in_expr,
            }) => IExpr::Duplication(Duplication {
                tag,
                pair,
                to_clone: Box::new(inline(*to_clone, def_table)),
                in_expr: Box::new(inline(*in_expr, def_table)),
            }),
            IExpr::Superposition(Superposition { tag, lhs, rhs }) => {
                IExpr::Superposition(Superposition {
                    tag,
                    lhs: Box::new(inline(*lhs, def_table)),
                    rhs: Box::new(inline(*rhs, def_table)),
                })
            }
            IExpr::Variable(v) => def_table.get(&v.0).cloned().unwrap_or(IExpr::Variable(v)),
        }
    }

    let inlined = inline(expr, &def_table);

    let _ = cc_expr(inlined, &mut net, &mut tags, &mut names);

    net
}

pub fn compile_sk(e: SkExpr) -> AstPort {
    let mut names = NameIter::default();

    let cc = build_compilation_expr(e, &mut names);

    cc.clone().iter_tree().for_each(|x| {
        x.expand_step(&mut names);
    });

    let combinated = cc.combinate(&mut names);

    println!("combinated: {}", combinated);

    combinated
}

pub fn decode_sk(p: &AstPort) -> SkExpr {
    tracing::trace!("decoding {}", p);

    OwnedNetBuilder::decombinate(p).expect("invalid SK expression")
}

fn build_compilation_expr(e: SkExpr, names: &mut NameIter) -> OwnedNetBuilder {
    tracing::trace!("compiling {:?}", e);

    let best_port = |p: &OwnedNetBuilder| -> (usize, OwnedNetBuilder) {
        p.clone()
            .iter_tree()
            .map(|x| {
                x.0.borrow()
                    .builder
                    .iter_ports()
                    .enumerate()
                    .filter(|(_, p)| {
                        p.is_none()
                            || p.map(|p| {
                                matches!(p.1 .0.borrow().builder, SkCombinatorBuilder::Var { .. })
                            })
                            .unwrap_or_default()
                    })
                    .map(|(i, _)| (i, x.clone()))
                    .next()
            })
            .flatten()
            .next()
            .unwrap_or((1, p.clone()))
    };

    let e_trans = match e.clone() {
        SkExpr::Var(v) => OwnedNetBuilder::new(
            SkCombinatorBuilder::Var {
                name: v,
                primary_port: None,
            },
            names,
        ),
        SkExpr::K(a, b) => {
            let temp_empty_var = OwnedNetBuilder::new(
                SkCombinatorBuilder::Var {
                    name: names.next_var_name(),
                    primary_port: None,
                },
                names,
            );
            let e = OwnedNetBuilder::new(
                SkCombinatorBuilder::K {
                    primary_port: Some((0, temp_empty_var.clone())),
                },
                names,
            );
            temp_empty_var
                .update_with(|builder| builder.clone().with_primary_port(Some((0, e.clone()))));

            let a_cc = a.map(|a| build_compilation_expr(*a, names));

            if let Some(a_port) = a_cc.map(|a| best_port(&a)) {
                let empty_port_var = OwnedNetBuilder::new(
                    SkCombinatorBuilder::Var {
                        name: names.next_var_name(),
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
                        .with_port_i(a_port.0, Some((2, e_parent.clone())))
                });

                let b_port = b
                    .map(|b| build_compilation_expr(*b, names))
                    .map(|b| best_port(&b))
                    .expect("malformed expr");

                let empty_port_var = OwnedNetBuilder::new(
                    SkCombinatorBuilder::Var {
                        name: names.next_var_name(),
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
                        .with_port_i(b_port.0, Some((2, constr_parent.clone())))
                });

                e_parent.update_with(|builder| {
                    builder
                        .clone()
                        .with_aux_port_i(0, Some((0, constr_parent.clone())))
                });

                e.update_with(|builder| {
                    builder
                        .clone()
                        .with_primary_port(Some((0, e_parent.clone())))
                });
            };

            e
        }
        SkExpr::S(a, b, c) => {
            let temp_empty_var = OwnedNetBuilder::new(
                SkCombinatorBuilder::Var {
                    name: names.next_var_name(),
                    primary_port: None,
                },
                names,
            );
            let e = OwnedNetBuilder::new(
                SkCombinatorBuilder::S {
                    primary_port: Some((0, temp_empty_var.clone())),
                },
                names,
            );
            temp_empty_var
                .update_with(|builder| builder.clone().with_primary_port(Some((0, e.clone()))));

            let a_cc = a.map(|a| build_compilation_expr(*a, names));

            if let Some(a_port) = a_cc.map(|a| best_port(&a)) {
                let empty_port_var = OwnedNetBuilder::new(
                    SkCombinatorBuilder::Var {
                        name: names.next_var_name(),
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
                        .with_port_i(a_port.0, Some((2, e_parent.clone())))
                });

                let b_port = b
                    .map(|b| build_compilation_expr(*b, names))
                    .map(|b| best_port(&b))
                    .expect("malformed expr");

                let empty_port_var = OwnedNetBuilder::new(
                    SkCombinatorBuilder::Var {
                        name: names.next_var_name(),
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
                        .with_port_i(b_port.0, Some((2, constr_parent.clone())))
                });

                e_parent.update_with(|builder| {
                    builder
                        .clone()
                        .with_aux_port_i(0, Some((0, constr_parent.clone())))
                });

                e.update_with(|builder| {
                    builder
                        .clone()
                        .with_primary_port(Some((0, e_parent.clone())))
                });

                let c_port = c
                    .map(|c| build_compilation_expr(*c, names))
                    .map(|c| best_port(&c))
                    .expect("malformed expr");

                let empty_port_var = OwnedNetBuilder::new(
                    SkCombinatorBuilder::Var {
                        name: names.next_var_name(),
                        primary_port: None,
                    },
                    names,
                );
                let constr_parent_parent = OwnedNetBuilder::new(
                    SkCombinatorBuilder::Constr {
                        primary_port: Some((1, constr_parent.clone())),
                        aux_ports: [Some((0, empty_port_var.clone())), Some(c_port.clone())],
                    },
                    names,
                );

                empty_port_var.update_with(|builder| {
                    builder
                        .clone()
                        .with_primary_port(Some((1, constr_parent_parent.clone())))
                });

                c_port.1.update_with(|builder| {
                    builder
                        .clone()
                        .with_port_i(c_port.0, Some((2, constr_parent_parent.clone())))
                });

                constr_parent.update_with(|builder| {
                    builder
                        .clone()
                        .with_aux_port_i(0, Some((0, constr_parent_parent.clone())))
                });

                e.update_with(|builder| {
                    builder
                        .clone()
                        .with_primary_port(Some((0, e_parent.clone())))
                });
            };

            e
        }
    };

    e_trans
        .clone()
        .iter_tree()
        .for_each(|x| tracing::trace!("encoding {} -> {:?}", e.clone(), x));

    e_trans
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
    use inetlib::reducers::combinators::reduce_dyn;

    #[test_log::test]
    fn test_eval_k_simple() {
        let (case, expected) = ("(K)", "(K)");

        let parsed = parser().parse(lexer().parse(case).unwrap()).unwrap();
        let compiled = compile_sk(parsed.into());

        let result = reduce_dyn(&compiled);

        assert_eq!(decode_sk(&result[0].orient()).to_string(), expected);
    }

    #[test_log::test]
    fn test_eval_k_call() {
        let (case, expected) = ("(K(K)(K))", "(K)");

        let parsed = parser().parse(lexer().parse(case).unwrap()).unwrap();
        let compiled = compile_sk(parsed.into());

        let result = reduce_dyn(&compiled);

        assert_eq!(decode_sk(&result[0].orient()).to_string(), expected);
    }

    #[test_log::test]
    fn test_cc_icalc_simple() {
        let case = "(\\x x a)";

        let parsed = parser_icalc::parser()
            .parse(
                parser_icalc::lexer()
                    .parse(case)
                    .unwrap()
                    .into_iter()
                    .flatten()
                    .collect::<Vec<_>>(),
            )
            .unwrap();

        let cc = compile_icalc(parsed.into_iter().map(|x| x.0).collect());

        assert_eq!(cc[0].to_string(), "Constr[@2](x, x) >< Constr[@5](ret, a)");
    }
}
