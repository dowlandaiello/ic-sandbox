use super::{
    builder::{CombinatorBuilder as RawCombinatorBuilder, OwnedNetBuilder},
    CombinatorBuilder,
};
use crate::parser::Expr;
use inetlib::{
    parser::{
        ast_combinators::{Constructor, Expr as CExpr, IndexedPort, Port},
        naming::NameIter,
    },
    reducers::combinators::reduce_dyn,
};
use std::collections::BTreeMap;

pub fn decompile(
    p: &Port,
    names: &NameIter,
    bind_ids_for_ports: &mut BTreeMap<IndexedPort, String>,
) -> Expr {
    let p = p.orient();

    tracing::debug!("decoding {}", p.iter_tree_visitor().into_string());

    // A constr can indicate an abstraction
    // or an application.
    // We can differentiate the two since an abstraction will always be encodced.
    // That is, its root is a Z_4 node.
    // We will want to start our decompilation at the root of the expression, however.
    // This is indicated by the position of v
    // Let us start with application

    let p_combinator = { p.borrow().clone() };

    match p_combinator {
        CExpr::Constr(Constructor { aux_ports, .. }) => {
            let mut p_aux = aux_ports
                .iter()
                .filter_map(|x| Some(x.as_ref()?.1.borrow().clone()));

            // This is an abstraction
            match (p_aux.next().unwrap(), p_aux.next().unwrap()) {
                (CExpr::Constr(_), CExpr::Constr(_)) => {
                    let decoder = OwnedNetBuilder::new(
                        RawCombinatorBuilder::D {
                            primary_port: None,
                            aux_port: None,
                        },
                        names,
                    );

                    let v = OwnedNetBuilder::new(
                        RawCombinatorBuilder::Var {
                            name: names.next_var_name(),
                            primary_port: None,
                        },
                        names,
                    );

                    OwnedNetBuilder::connect((0, v.clone()), (1, decoder.clone()));

                    let decoder = decoder.expand_step(names).combinate();

                    {
                        decoder.borrow_mut().set_primary_port(Some((0, p.clone())));
                        p.borrow_mut().set_primary_port(Some((0, decoder.clone())));
                    }

                    tracing::trace!(
                        "decoding abstraction with decoder: {} {}",
                        p.iter_tree_visitor().into_string(),
                        decoder.iter_tree_visitor().into_string(),
                    );

                    // X: aux_ports[0]
                    // body: aux_ports[1]

                    let decoded_abstr_root = reduce_dyn(&p).remove(0);

                    tracing::trace!(
                        "decoded abstraction: {}",
                        decoded_abstr_root.iter_tree_visitor().into_string()
                    );

                    let abstr_aux = {
                        decoded_abstr_root
                            .borrow()
                            .aux_ports()
                            .into_iter()
                            .cloned()
                            .collect::<Vec<_>>()
                    };

                    let bind_id = names.next_var_name();

                    bind_ids_for_ports.insert((1, decoded_abstr_root), bind_id.clone());

                    if let Some(inner_bind_id) =
                        bind_ids_for_ports.get(&abstr_aux[1].as_ref().unwrap())
                    {
                        Expr::Abstraction {
                            bind_id: bind_id.clone(),
                            body: Box::new(Expr::Id(inner_bind_id.to_owned())),
                        }
                    } else {
                        Expr::Abstraction {
                            bind_id: bind_id.clone(),
                            body: Box::new(decompile(
                                &abstr_aux[1].as_ref().unwrap().1,
                                names,
                                bind_ids_for_ports,
                            )),
                        }
                    }
                }
                _ => unreachable!(),
            }
        }
        CExpr::Var(v) => {
            if v.name.0.starts_with("v") {
                decompile(&v.port.as_ref().unwrap().1, names, bind_ids_for_ports)
            } else {
                Expr::Id(v.name.0.clone())
            }
        }
        _ => unreachable!(),
    }
}

pub fn compile(e: Expr, names: &NameIter) -> Port {
    let cc = build_compilation_expr(e.clone(), &names);

    cc.clone().iter_tree().for_each(|x| {
        x.expand_step(&names);
    });

    #[cfg(test)]
    cc.checksum();

    let combinated = cc.combinate();

    tracing::debug!(
        "encoded {} -> {}",
        e,
        combinated.iter_tree_visitor().into_string()
    );

    combinated
}

pub(crate) fn build_compilation_expr(e: Expr, names: &NameIter) -> OwnedNetBuilder {
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
                                p.1 .0
                                    .borrow()
                                    .builder
                                    .as_var()
                                    .map(|x| x.starts_with("v"))
                                    .unwrap_or_default()
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

    let id_ports = |p: OwnedNetBuilder, id: &str| -> Vec<(usize, OwnedNetBuilder)> {
        p.clone()
            .iter_tree()
            .map(|x| {
                x.0.borrow()
                    .builder
                    .iter_ports()
                    .enumerate()
                    .filter_map(|(i, p)| Some((i, p?)))
                    .filter(|(_, p)| {
                        p.1 .0
                            .borrow()
                            .builder
                            .as_var()
                            .map(|x| x == id)
                            .unwrap_or_default()
                    })
                    .map(|(i, _)| (i, x.clone()))
                    .next()
            })
            .flatten()
            .collect()
    };

    let res = match e.clone() {
        Expr::Id(x) => OwnedNetBuilder::new(
            RawCombinatorBuilder::Var {
                name: x,
                primary_port: None,
            },
            names,
        ),
        Expr::Abstraction { body, bind_id } => {
            let body_cc = build_compilation_expr(*body, names);
            let constr = OwnedNetBuilder::new(
                RawCombinatorBuilder::Constr {
                    primary_port: None,
                    aux_ports: [const { None }; 2],
                },
                names,
            );

            let var = OwnedNetBuilder::new(
                RawCombinatorBuilder::Var {
                    name: names.next_var_name(),
                    primary_port: None,
                },
                names,
            );

            OwnedNetBuilder::connect((2, constr.clone()), best_port(&body_cc));

            // TODO: Need to handle multiple occurrences of bind_id

            let bind_id_ports = id_ports(body_cc.clone(), &bind_id);

            match bind_id_ports.as_slice() {
                [] => {
                    let era = OwnedNetBuilder::new(
                        RawCombinatorBuilder::Era { primary_port: None },
                        names,
                    );

                    OwnedNetBuilder::connect((0, era.clone()), (1, constr.clone()));
                }
                [x] => {
                    OwnedNetBuilder::connect((1, constr.clone()), x.clone());
                }
                xs => {
                    xs.iter()
                        .enumerate()
                        .fold((1, constr.clone()), |acc, (i, x)| {
                            if i == xs.len() - 1 {
                                OwnedNetBuilder::connect(x.clone(), acc.clone());

                                return acc;
                            }

                            let dup = OwnedNetBuilder::new(
                                RawCombinatorBuilder::Dup {
                                    primary_port: None,
                                    aux_ports: [const { None }; 2],
                                },
                                names,
                            );

                            OwnedNetBuilder::connect((0, dup.clone()), acc);
                            OwnedNetBuilder::connect((1, dup.clone()), x.clone());

                            (2, dup)
                        });
                }
            }
            OwnedNetBuilder::connect((0, var.clone()), (0, constr.clone()));

            constr.encode(names)
        }
        Expr::Application { lhs, rhs } => {
            let lhs_cc = build_compilation_expr(*lhs, names);
            let rhs_cc = build_compilation_expr(*rhs, names);

            let constr_app = OwnedNetBuilder::new(
                RawCombinatorBuilder::Constr {
                    primary_port: None,
                    aux_ports: [const { None }; 2],
                },
                names,
            );
            let dec = OwnedNetBuilder::new(
                RawCombinatorBuilder::D {
                    primary_port: None,
                    aux_port: None,
                },
                names,
            );

            let var = OwnedNetBuilder::new(
                RawCombinatorBuilder::Var {
                    name: names.next_var_name(),
                    primary_port: None,
                },
                names,
            );

            OwnedNetBuilder::connect((0, constr_app.clone()), (1, dec.clone()));
            OwnedNetBuilder::connect((0, dec.clone()), best_port(&lhs_cc));
            OwnedNetBuilder::connect((1, constr_app.clone()), best_port(&rhs_cc));
            OwnedNetBuilder::connect((2, constr_app.clone()), (0, var.clone()));

            constr_app
        }
    };

    tracing::debug!(
        "encoding {} -> {}",
        e.clone(),
        res.clone().iter_tree().into_string()
    );

    res
}
