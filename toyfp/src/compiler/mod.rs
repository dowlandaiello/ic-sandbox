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

    let cc = build_compilation_expr(e, false, &mut names);
    cc.expand_step(&mut names);

    cc.combinate(&mut Default::default(), &mut names)
}

pub fn decode_sk(p: &AstPort) -> SkExpr {
    tracing::trace!("decoding {}", p);

    OwnedNetBuilder::decombinate(p).expect("invalid SK expression")
}

fn build_compilation_expr(e: SkExpr, code: bool, names: &mut NameIter) -> OwnedNetBuilder {
    tracing::trace!("compiling {:?}", e);

    match e {
        SkExpr::Var(v) => OwnedNetBuilder::new(
            if code {
                SkCombinatorBuilder::Code(Box::new(SkCombinatorBuilder::Var {
                    name: v,
                    primary_port: None,
                }))
            } else {
                SkCombinatorBuilder::Var {
                    name: v,
                    primary_port: None,
                }
            },
            names,
        ),
        SkExpr::K(a, b) => {
            let temp_empty_var = OwnedNetBuilder::new(
                SkCombinatorBuilder::Var {
                    name: names.next(),
                    primary_port: None,
                },
                names,
            );
            let e = OwnedNetBuilder::new(
                if code {
                    SkCombinatorBuilder::Code(Box::new(SkCombinatorBuilder::K {
                        primary_port: Some((0, temp_empty_var.clone())),
                    }))
                } else {
                    SkCombinatorBuilder::K {
                        primary_port: Some((0, temp_empty_var.clone())),
                    }
                },
                names,
            );
            temp_empty_var
                .update_with(|builder| builder.clone().with_primary_port(Some((0, e.clone()))));

            let a_cc = a.map(|a| build_compilation_expr(*a, true, names));

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

                let b_port = b
                    .map(|b| build_compilation_expr(*b, true, names))
                    .map(|b| (0, b))
                    .expect("malformed expr");

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
                    name: names.next(),
                    primary_port: None,
                },
                names,
            );
            let e = OwnedNetBuilder::new(
                if code {
                    SkCombinatorBuilder::Code(Box::new(SkCombinatorBuilder::S {
                        primary_port: Some((0, temp_empty_var.clone())),
                    }))
                } else {
                    SkCombinatorBuilder::S {
                        primary_port: Some((0, temp_empty_var.clone())),
                    }
                },
                names,
            );
            temp_empty_var
                .update_with(|builder| builder.clone().with_primary_port(Some((0, e.clone()))));

            let a_cc = a.map(|a| build_compilation_expr(*a, true, names));

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

                let b_port = b
                    .map(|b| build_compilation_expr(*b, true, names))
                    .map(|b| (0, b))
                    .expect("malformed expr");

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
                        .with_aux_port_i(0, Some((0, constr_parent.clone())))
                });

                e.update_with(|builder| {
                    builder
                        .clone()
                        .with_primary_port(Some((0, e_parent.clone())))
                });

                let c_port = c
                    .map(|c| build_compilation_expr(*c, true, names))
                    .map(|c| (0, c))
                    .expect("malformed expr");

                let empty_port_var = OwnedNetBuilder::new(
                    SkCombinatorBuilder::Var {
                        name: names.next(),
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
                        .with_primary_port(Some((2, constr_parent_parent.clone())))
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
    use inetlib::reducers::combinators::reduce_dyn;

    #[test_log::test]
    fn test_eval_k_simple() {
        let (case, expected) = ("(K)", "(K)");

        let parsed = parser().parse(lexer().parse(case).unwrap()).unwrap();
        let compiled = compile_sk(parsed.into());

        let result = reduce_dyn(&compiled).unwrap();

        assert_eq!(decode_sk(&result[0].orient()).to_string(), expected);
    }

    #[test_log::test]
    fn test_eval_k_call() {
        let (case, expected) = ("(K(K)(K))", "(K)");

        let parsed = parser().parse(lexer().parse(case).unwrap()).unwrap();
        let compiled = compile_sk(parsed.into());

        let result = reduce_dyn(&compiled).unwrap();

        assert_eq!(decode_sk(&result[0].orient()).to_string(), expected);
    }
}
