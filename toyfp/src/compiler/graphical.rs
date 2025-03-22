use super::{
    builder::{CombinatorBuilder as RawCombinatorBuilder, OwnedNetBuilder},
    CombinatorBuilder,
};
use crate::parser::Expr;
use inetlib::parser::{ast_combinators::Port, naming::NameIter};

pub fn compile(e: Expr) -> Port {
    let names = NameIter::default();

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

            OwnedNetBuilder::connect((2, constr.clone()), (0, body_cc.clone()));
            OwnedNetBuilder::connect((1, constr.clone()), (0, dec.clone()));

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
                    OwnedNetBuilder::connect((1, dec.clone()), x.clone());
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

                            (1, dup)
                        });
                }
            }
            OwnedNetBuilder::connect((0, var.clone()), (0, constr.clone()));

            constr
        }
        Expr::Application { lhs, rhs } => {
            let lhs_cc = build_compilation_expr(*lhs, names);
            let rhs_cc = build_compilation_expr(*rhs, names).encode(names);

            let constr_app = OwnedNetBuilder::new(
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

            OwnedNetBuilder::connect((0, constr_app.clone()), best_port(&lhs_cc));
            OwnedNetBuilder::connect((1, constr_app.clone()), best_port(&rhs_cc));
            OwnedNetBuilder::connect((2, constr_app.clone()), (0, var.clone()));

            best_port(&constr_app).1
        }
    };

    tracing::debug!(
        "encoding {} -> {}",
        e.clone(),
        res.clone().iter_tree().into_string()
    );

    res
}
