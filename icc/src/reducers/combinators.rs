use crate::parser::{
    ast_combinators::{Constructor, Duplicator, Eraser, Expr, Port},
    naming::NameIter,
};

#[cfg(not(feature = "threadpool"))]
pub fn reduce_dyn(e: &Port) -> Option<Vec<Port>> {
    let reduced = reduce_step_dyn(e)?;

    if reduced.len() <= 1 {
        Some(reduced)
    } else {
        Some(
            reduced
                .into_iter()
                .filter_map(|p| reduce_dyn(&p))
                .flatten()
                .collect(),
        )
    }
}

#[cfg(feature = "threadpool")]
pub fn reduce_dyn(e: &Port) -> Option<Vec<Port>> {
    use rayon::iter::{IntoParallelIterator, ParallelIterator};

    let reduced = reduce_step_dyn(e)?;

    if reduced.len() <= 1 {
        Some(reduced)
    } else {
        Some(
            reduced
                .into_par_iter()
                .filter_map(|p| reduce_dyn(&p))
                .flatten()
                .collect(),
        )
    }
}

pub fn reduce_step_dyn(e: &Port) -> Option<Vec<Port>> {
    let mut names = NameIter::default();

    let (e, e2) = if let Some(active_pair) = e.try_as_active_pair() {
        active_pair
    } else {
        return Some(vec![e.clone()]);
    };

    let (lhs, rhs) = (e.borrow(), e2.borrow());

    match (&*lhs, &*rhs) {
        // commutation of constr >< dup
        (&Expr::Constr(ref c), &Expr::Dup(ref d)) => {
            let original_ports = [
                c.aux_ports[0].clone(),
                c.aux_ports[1].clone(),
                d.aux_ports[0].clone(),
                d.aux_ports[1].clone(),
            ];

            make_constr_dup_commutation_net(original_ports, e.clone(), e2.clone(), &mut names)
        }
        (&Expr::Dup(ref d), &Expr::Constr(ref c)) => {
            let original_ports = [
                c.aux_ports[0].clone(),
                c.aux_ports[1].clone(),
                d.aux_ports[0].clone(),
                d.aux_ports[1].clone(),
            ];

            make_constr_dup_commutation_net(original_ports, e2.clone(), e.clone(), &mut names)
        }
        // commutation of constr >< era
        (&Expr::Constr(ref c), &Expr::Era(_)) => {
            let original_ports = [c.aux_ports[0].clone(), c.aux_ports[1].clone()];

            make_constr_era_commutation_net(original_ports, e.clone(), &mut names)
        }
        (&Expr::Era(_), &Expr::Constr(ref c)) => {
            let original_ports = [c.aux_ports[0].clone(), c.aux_ports[1].clone()];

            make_constr_era_commutation_net(original_ports, e2.clone(), &mut names)
        }
        // Commutation of dup >< era
        (&Expr::Dup(ref c), &Expr::Era(_)) => {
            let original_ports = [c.aux_ports[0].clone(), c.aux_ports[1].clone()];

            make_constr_era_commutation_net(original_ports, e.clone(), &mut names)
        }
        (&Expr::Era(_), &Expr::Dup(ref c)) => {
            let original_ports = [c.aux_ports[0].clone(), c.aux_ports[1].clone()];

            make_constr_era_commutation_net(original_ports, e2.clone(), &mut names)
        }
        // Annihiliation of Constr
        (&Expr::Constr(ref c), &Expr::Constr(ref d)) => {
            let original_ports = [
                c.aux_ports[0].clone(),
                d.aux_ports[1].clone(),
                c.aux_ports[1].clone(),
                d.aux_ports[0].clone(),
            ];

            if let Some(p) = original_ports[0].as_ref() {
                p.borrow_mut().swap_conn(&e, original_ports[1].clone());
            }
            if let Some(p) = original_ports[1].as_ref() {
                p.borrow_mut().swap_conn(&e2, original_ports[0].clone());
            }
            if let Some(p) = original_ports[2].as_ref() {
                p.borrow_mut().swap_conn(&e, original_ports[3].clone());
            }
            if let Some(p) = original_ports[3].as_ref() {
                p.borrow_mut().swap_conn(&e2, original_ports[2].clone());
            }

            Some(
                [&original_ports[0], &original_ports[2]]
                    .into_iter()
                    .filter_map(|x| x.as_ref())
                    .cloned()
                    .collect(),
            )
        }
        // Annihiliation of Constr
        (&Expr::Dup(ref c), &Expr::Dup(ref d)) => {
            let original_ports = [
                c.aux_ports[0].clone(),
                d.aux_ports[1].clone(),
                c.aux_ports[1].clone(),
                d.aux_ports[0].clone(),
            ];

            if let Some(p) = original_ports[0].as_ref() {
                p.borrow_mut().swap_conn(&e, original_ports[1].clone());
            }
            if let Some(p) = original_ports[1].as_ref() {
                p.borrow_mut().swap_conn(&e2, original_ports[0].clone());
            }
            if let Some(p) = original_ports[2].as_ref() {
                p.borrow_mut().swap_conn(&e, original_ports[3].clone());
            }
            if let Some(p) = original_ports[3].as_ref() {
                p.borrow_mut().swap_conn(&e2, original_ports[2].clone());
            }

            Some(
                [&original_ports[0], &original_ports[2]]
                    .into_iter()
                    .filter_map(|x| x.as_ref())
                    .cloned()
                    .collect(),
            )
        }
        // Anihilation of era
        (&Expr::Era(_), &Expr::Era(_)) => Some(Vec::new()),
        // No rule for vars
        _ => None,
    }
}

// TODO: do this with adjacency matrix, perhaps
// for a single owner, no refcell necessary
fn make_constr_dup_commutation_net(
    original_ports: [Option<Port>; 4],
    lhs: Port,
    rhs: Port,
    names_iter: &mut NameIter,
) -> Option<Vec<Port>> {
    let top_lhs: Port = Expr::Dup(Duplicator::new()).into_port(names_iter);
    let top_rhs: Port = Expr::Dup(Duplicator::new()).into_port(names_iter);

    let bot_lhs: Port = Expr::Constr(Constructor::new()).into_port(names_iter);
    let bot_rhs: Port = Expr::Constr(Constructor::new()).into_port(names_iter);

    top_lhs
        .borrow_mut()
        .set_aux_ports([Some(bot_lhs.clone()), Some(bot_rhs.clone())]);
    top_rhs
        .borrow_mut()
        .set_aux_ports([Some(bot_lhs.clone()), Some(bot_rhs.clone())]);
    bot_lhs
        .borrow_mut()
        .set_aux_ports([Some(top_lhs.clone()), Some(top_rhs.clone())]);
    bot_rhs
        .borrow_mut()
        .set_aux_ports([Some(top_lhs.clone()), Some(top_rhs.clone())]);

    // Connect original top left, top right, bottom left, bottom right vars
    // to new agents
    match &original_ports {
        [a, b, c, d] => {
            top_lhs.borrow_mut().set_primary_port(a.clone());
            top_rhs.borrow_mut().set_primary_port(b.clone());
            bot_lhs.borrow_mut().set_primary_port(c.clone());
            bot_rhs.borrow_mut().set_primary_port(d.clone());
        }
    }

    if let Some(top_left) = &original_ports[0] {
        top_left.borrow_mut().swap_conn(&lhs, Some(top_lhs.clone()));
    }

    if let Some(top_right) = &original_ports[1] {
        top_right
            .borrow_mut()
            .swap_conn(&lhs, Some(top_rhs.clone()));
    }

    if let Some(bot_left) = &original_ports[2] {
        bot_left.borrow_mut().swap_conn(&rhs, Some(bot_lhs.clone()));
    }

    if let Some(bot_right) = &original_ports[3] {
        bot_right
            .borrow_mut()
            .swap_conn(&rhs, Some(bot_rhs.clone()));
    }

    Some(vec![top_lhs])
}

fn make_constr_era_commutation_net(
    original_ports: [Option<Port>; 2],
    lhs: Port,
    names_iter: &mut NameIter,
) -> Option<Vec<Port>> {
    let era_lhs: Port = Expr::Era(Eraser::new()).into_port(names_iter);
    let era_rhs: Port = Expr::Era(Eraser::new()).into_port(names_iter);

    era_lhs
        .borrow_mut()
        .set_primary_port(original_ports[0].clone());
    era_rhs
        .borrow_mut()
        .set_primary_port(original_ports[1].clone());

    if let Some(top_left) = &original_ports[0] {
        top_left.borrow_mut().swap_conn(&lhs, Some(era_lhs.clone()));
    }

    if let Some(top_right) = &original_ports[1] {
        top_right
            .borrow_mut()
            .swap_conn(&lhs, Some(era_rhs.clone()));
    }

    Some(vec![era_lhs, era_rhs])
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::parser::{ast_combinators::Var, ast_lafont::Ident};

    #[test]
    fn test_reduce_commute_dup_constr() {
        let mut names_iter = NameIter::default();

        let top: Port = Expr::Constr(Constructor::new()).into_port(&mut names_iter);
        let bottom: Port = Expr::Dup(Duplicator::new()).into_port(&mut names_iter);

        top.borrow_mut().set_primary_port(Some(bottom.clone()));
        bottom.borrow_mut().set_primary_port(Some(top.clone()));

        let vars = [
            Expr::Var(Var {
                name: Ident(names_iter.next()),
                port: Some(top.clone()),
            })
            .into_port(&mut names_iter),
            Expr::Var(Var {
                name: Ident(names_iter.next()),
                port: Some(top.clone()),
            })
            .into_port(&mut names_iter),
            Expr::Var(Var {
                name: Ident(names_iter.next()),
                port: Some(bottom.clone()),
            })
            .into_port(&mut names_iter),
            Expr::Var(Var {
                name: Ident(names_iter.next()),
                port: Some(bottom.clone()),
            })
            .into_port(&mut names_iter),
        ];

        top.borrow_mut()
            .set_aux_ports([Some(vars[0].clone()), Some(vars[1].clone())]);
        bottom
            .borrow_mut()
            .set_aux_ports([Some(vars[2].clone()), Some(vars[3].clone())]);

        let res = reduce_dyn(&top).unwrap();
        assert_eq!(
            res[0].to_string(),
            "Dup[@0](0, Constr[@2](2, @0, Dup[@1](1, @2, Constr[@3](3, @0, @1))), @3)"
        );
    }

    #[test]
    fn test_reduce_commute_symmetric_era() {
        let cases = [
            (Expr::Constr(Constructor::new()), Expr::Era(Eraser::new())),
            (Expr::Dup(Duplicator::new()), Expr::Era(Eraser::new())),
        ];

        for (top_expr, bottom_expr) in cases {
            let mut names_iter = NameIter::default();

            let top: Port = top_expr.into_port(&mut names_iter);
            let bottom: Port = bottom_expr.into_port(&mut names_iter);

            top.borrow_mut().set_primary_port(Some(bottom.clone()));
            bottom.borrow_mut().set_primary_port(Some(top.clone()));

            let vars = [
                Expr::Var(Var {
                    name: Ident(names_iter.next()),
                    port: Some(top.clone()),
                })
                .into_port(&mut names_iter),
                Expr::Var(Var {
                    name: Ident(names_iter.next()),
                    port: Some(top.clone()),
                })
                .into_port(&mut names_iter),
            ];

            top.borrow_mut()
                .set_aux_ports([Some(vars[0].clone()), Some(vars[1].clone())]);

            let res = reduce_dyn(&top).unwrap();
            assert_eq!(res[0].to_string(), "Era[@0](0)");
            assert_eq!(res[1].to_string(), "Era[@1](1)");
        }
    }

    #[test]
    fn test_reduce_annihilate_symmetric() {
        let cases = [
            (
                Expr::Constr(Constructor::new()),
                Expr::Constr(Constructor::new()),
            ),
            (Expr::Dup(Duplicator::new()), Expr::Dup(Duplicator::new())),
        ];

        for (top_expr, bottom_expr) in cases {
            let mut names_iter = NameIter::default();

            let top: Port = top_expr.into_port(&mut names_iter);
            let bottom: Port = bottom_expr.into_port(&mut names_iter);

            top.borrow_mut().set_primary_port(Some(bottom.clone()));
            bottom.borrow_mut().set_primary_port(Some(top.clone()));

            let vars = [
                Expr::Var(Var {
                    name: Ident(names_iter.next()),
                    port: Some(top.clone()),
                })
                .into_port(&mut names_iter),
                Expr::Var(Var {
                    name: Ident(names_iter.next()),
                    port: Some(top.clone()),
                })
                .into_port(&mut names_iter),
                Expr::Var(Var {
                    name: Ident(names_iter.next()),
                    port: Some(bottom.clone()),
                })
                .into_port(&mut names_iter),
                Expr::Var(Var {
                    name: Ident(names_iter.next()),
                    port: Some(bottom.clone()),
                })
                .into_port(&mut names_iter),
            ];

            top.borrow_mut()
                .set_aux_ports([Some(vars[0].clone()), Some(vars[1].clone())]);
            bottom
                .borrow_mut()
                .set_aux_ports([Some(vars[2].clone()), Some(vars[3].clone())]);

            let res = reduce_dyn(&top).unwrap();
            assert_eq!(res[0].to_string(), "0 ~ 3");
            assert_eq!(res[1].to_string(), "1 ~ 2");
        }
    }

    #[test]
    fn test_reduce_annihilate_era_era() {
        let mut names_iter = NameIter::default();

        let top: Port = Expr::Era(Eraser::new()).into_port(&mut names_iter);
        let bottom: Port = Expr::Era(Eraser::new()).into_port(&mut names_iter);

        top.borrow_mut().set_primary_port(Some(bottom.clone()));
        bottom.borrow_mut().set_primary_port(Some(top.clone()));

        let res = reduce_dyn(&top);
        assert!(res.unwrap().is_empty());
    }
}
