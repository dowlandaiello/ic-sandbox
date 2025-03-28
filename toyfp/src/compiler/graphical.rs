use super::{
    builder::{CombinatorBuilder as RawCombinatorBuilder, OwnedNetBuilder},
    typing::UntypedExpr,
    CombinatorBuilder,
};
use inetlib::{
    parser::{
        ast_combinators::{Constructor, Duplicator, Expr as CExpr, Port},
        naming::NameIter,
    },
    reducers::combinators::reduce_dyn,
};
use std::{collections::BTreeMap, iter};

pub fn decompile(
    p: &Port,
    names: &NameIter,
    bind_ids_for_ports: &mut BTreeMap<Vec<usize>, String>,
) -> UntypedExpr {
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
        CExpr::Constr(Constructor { .. }) => {
            // This is an abstraction
            let decoder = OwnedNetBuilder::new(
                RawCombinatorBuilder::D {
                    primary_port: None,
                    aux_port: None,
                },
                names,
            );

            let decoder = decoder.expand_step(names).combinate();

            {
                let conn_rest_port = p.borrow().primary_port().unwrap().clone();
                conn_rest_port
                    .1
                    .borrow_mut()
                    .insert_port_i(conn_rest_port.0, Some((2, decoder.clone())));
                decoder
                    .borrow_mut()
                    .insert_aux_port(1, Some(conn_rest_port.clone()));

                decoder.borrow_mut().set_primary_port(Some((0, p.clone())));
                p.borrow_mut().set_primary_port(Some((0, decoder.clone())));
            }

            tracing::trace!(
                "decoding abstraction: {}",
                p.iter_tree_visitor().into_string(),
            );

            // X: aux_ports[0]
            // body: aux_ports[1]

            #[cfg(not(feature = "threadpool"))]
            p.checksum();

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

            // Abstr will have one var or potentially duplications of the var
            // with chained dups.
            let mut curr = abstr_aux[0].as_ref().unwrap().1.clone();
            let mut parent_port = (1, decoded_abstr_root);

            fn node_position(p: &Port) -> Vec<usize> {
                match &*p.borrow() {
                    CExpr::Constr(Constructor { primary_port, .. })
                    | CExpr::Dup(Duplicator { primary_port, .. }) => match primary_port {
                        Some(p) => iter::once(p.0)
                            .chain(node_position(&p.1).into_iter())
                            .collect(),
                        None => Default::default(),
                    },
                    _ => Default::default(),
                }
            }

            loop {
                bind_ids_for_ports.insert(node_position(&parent_port.1), bind_id.clone());

                parent_port = (1, curr.clone());

                curr = if let Some(next) = curr.iter_ports().into_iter().nth(2).flatten() {
                    next.1
                } else {
                    break;
                };

                if !matches!(&*curr.borrow(), CExpr::Dup(_)) {
                    break;
                }
            }

            if let Some(inner_bind_id) =
                bind_ids_for_ports.get(&node_position(&abstr_aux[1].as_ref().unwrap().1))
            {
                UntypedExpr::Abstraction {
                    bind_id: bind_id.clone(),
                    body: Box::new(UntypedExpr::Id(inner_bind_id.to_owned())),
                }
            } else {
                let body_p = abstr_aux[1].as_ref().unwrap().1.clone();

                UntypedExpr::Abstraction {
                    bind_id: bind_id.clone(),
                    body: Box::new(decompile(&body_p, names, bind_ids_for_ports)),
                }
            }
        }
        CExpr::Var(v) => {
            if v.name.starts_with("v") {
                decompile(&v.port.as_ref().unwrap().1, names, bind_ids_for_ports)
            } else {
                UntypedExpr::Id(v.name.clone())
            }
        }
        _ => unreachable!(),
    }
}

pub fn compile(e: UntypedExpr, names: &NameIter) -> Port {
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

pub(crate) fn build_compilation_expr(e: UntypedExpr, names: &NameIter) -> OwnedNetBuilder {
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
        UntypedExpr::Id(x) => OwnedNetBuilder::new(
            RawCombinatorBuilder::Var {
                name: x,
                primary_port: None,
            },
            names,
        ),
        UntypedExpr::Abstraction { body, bind_id } => {
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
        UntypedExpr::Application { lhs, rhs } => {
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
