use crate::parser::{
    ast_combinators::{Constructor, Duplicator, Eraser, Expr, IndexedPort, Port},
    naming::NameIter,
};

#[cfg(not(feature = "threadpool"))]
pub fn reduce_dyn(e: &Port) -> Option<Vec<Port>> {
    tracing::debug!("-- begin reduction tree: {}", e);

    e.iter_tree()
        .for_each(|p| tracing::trace!("reducing: {:?}", p));

    tracing::trace!("-- end reduction tree");

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
    e.iter_tree()
        .for_each(|p| tracing::trace!("reducing: {:?}", p));

    tracing::trace!("\n");

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

    let (lhs, rhs) = { (e.1.borrow().clone(), e2.1.borrow().clone()) };

    match (lhs, rhs) {
        // commutation of constr >< dup
        (Expr::Constr(ref c), Expr::Dup(ref d)) => {
            let original_ports = [
                c.aux_ports[0].clone(),
                c.aux_ports[1].clone(),
                d.aux_ports[0].clone(),
                d.aux_ports[1].clone(),
            ];

            make_constr_dup_commutation_net(original_ports, &mut names)
        }
        (Expr::Dup(ref c), Expr::Constr(ref d)) => {
            let original_ports = [
                c.aux_ports[0].clone(),
                c.aux_ports[1].clone(),
                d.aux_ports[0].clone(),
                d.aux_ports[1].clone(),
            ];

            make_dup_constr_commutation_net(original_ports, &mut names)
        }
        // commutation of constr >< era
        (Expr::Constr(ref c), Expr::Era(_)) => {
            let original_ports = [c.aux_ports[0].clone(), c.aux_ports[1].clone()];

            make_constr_era_commutation_net(original_ports, &mut names)
        }
        (Expr::Era(_), Expr::Constr(ref c)) => {
            let original_ports = [c.aux_ports[0].clone(), c.aux_ports[1].clone()];

            make_constr_era_commutation_net(original_ports, &mut names)
        }
        // Commutation of dup >< era
        (Expr::Dup(ref c), Expr::Era(_)) => {
            let original_ports = [c.aux_ports[0].clone(), c.aux_ports[1].clone()];

            make_constr_era_commutation_net(original_ports, &mut names)
        }
        (Expr::Era(_), Expr::Dup(ref c)) => {
            let original_ports = [c.aux_ports[0].clone(), c.aux_ports[1].clone()];

            make_constr_era_commutation_net(original_ports, &mut names)
        }
        // Annihiliation of Constr
        (Expr::Constr(ref c), Expr::Constr(ref d)) => {
            let original_ports = [
                c.aux_ports[0].clone(),
                d.aux_ports[0].clone(),
                c.aux_ports[1].clone(),
                d.aux_ports[1].clone(),
            ];

            for p in original_ports.iter().filter_map(|x| x.as_ref()) {
                println!("{:?}", p.1);
            }

            if let Some((port, p)) = original_ports[0].as_ref() {
                p.borrow_mut().swap_conn(*port, original_ports[1].clone());
            }
            if let Some((port, p)) = original_ports[1].as_ref() {
                p.borrow_mut().swap_conn(*port, original_ports[0].clone());
            }
            if let Some((port, p)) = original_ports[2].as_ref() {
                p.borrow_mut().swap_conn(*port, original_ports[3].clone());
            }
            if let Some((port, p)) = original_ports[3].as_ref() {
                p.borrow_mut().swap_conn(*port, original_ports[2].clone());
            }

            Some(
                [&original_ports[0], &original_ports[2]]
                    .into_iter()
                    .filter_map(|x| x.as_ref())
                    .map(|(_, x)| x)
                    .cloned()
                    .collect(),
            )
        }
        // Annihiliation of Constr
        (Expr::Dup(ref c), Expr::Dup(ref d)) => {
            let original_ports = [
                c.aux_ports[0].clone(),
                d.aux_ports[0].clone(),
                c.aux_ports[1].clone(),
                d.aux_ports[1].clone(),
            ];

            if let Some((port, p)) = original_ports[0].as_ref() {
                p.borrow_mut().swap_conn(*port, original_ports[1].clone());
            }
            if let Some((port, p)) = original_ports[1].as_ref() {
                p.borrow_mut().swap_conn(*port, original_ports[0].clone());
            }
            if let Some((port, p)) = original_ports[2].as_ref() {
                p.borrow_mut().swap_conn(*port, original_ports[3].clone());
            }
            if let Some((port, p)) = original_ports[3].as_ref() {
                p.borrow_mut().swap_conn(*port, original_ports[2].clone());
            }

            Some(
                [&original_ports[0], &original_ports[2]]
                    .into_iter()
                    .filter_map(|x| x.as_ref())
                    .map(|(_, x)| x)
                    .cloned()
                    .collect(),
            )
        }
        // Anihilation of era
        (Expr::Era(_), Expr::Era(_)) => Some(Vec::new()),
        // No rule for vars
        _ => None,
    }
}

// TODO: do this with adjacency matrix, perhaps
// for a single owner, no refcell necessary
fn make_dup_constr_commutation_net(
    original_ports: [Option<IndexedPort>; 4],
    names_iter: &mut NameIter,
) -> Option<Vec<Port>> {
    let bot_lhs: Port = Expr::Dup(Duplicator::new()).into_port(names_iter);
    let bot_rhs: Port = Expr::Dup(Duplicator::new()).into_port(names_iter);

    let top_lhs: Port = Expr::Constr(Constructor::new()).into_port(names_iter);
    let top_rhs: Port = Expr::Constr(Constructor::new()).into_port(names_iter);

    top_lhs
        .borrow_mut()
        .set_aux_ports([Some((1, bot_rhs.clone())), Some((1, bot_lhs.clone()))]);
    top_rhs
        .borrow_mut()
        .set_aux_ports([Some((2, bot_rhs.clone())), Some((2, bot_lhs.clone()))]);
    bot_lhs
        .borrow_mut()
        .set_aux_ports([Some((2, top_lhs.clone())), Some((2, top_rhs.clone()))]);
    bot_rhs
        .borrow_mut()
        .set_aux_ports([Some((1, top_lhs.clone())), Some((1, top_rhs.clone()))]);

    // Connect original top left, top right, bottom left, bottom right vars
    // to new agents
    match &original_ports {
        [a, b, c, d] => {
            top_lhs.borrow_mut().set_primary_port(a.clone());
            top_rhs.borrow_mut().set_primary_port(b.clone());
            bot_lhs.borrow_mut().set_primary_port(d.clone());
            bot_rhs.borrow_mut().set_primary_port(c.clone());
        }
    }

    if let Some((p, top_left)) = &original_ports[0] {
        top_left
            .borrow_mut()
            .swap_conn(*p, Some((0, top_lhs.clone())));
    }

    if let Some((p, top_right)) = &original_ports[1] {
        top_right
            .borrow_mut()
            .swap_conn(*p, Some((0, top_rhs.clone())));
    }

    if let Some((p, bot_left)) = &original_ports[2] {
        bot_left
            .borrow_mut()
            .swap_conn(*p, Some((0, bot_rhs.clone())));
    }

    if let Some((p, bot_right)) = &original_ports[3] {
        bot_right
            .borrow_mut()
            .swap_conn(*p, Some((0, bot_lhs.clone())));
    }

    Some(vec![top_lhs])
}

fn make_constr_dup_commutation_net(
    original_ports: [Option<IndexedPort>; 4],
    names_iter: &mut NameIter,
) -> Option<Vec<Port>> {
    let bot_lhs: Port = Expr::Constr(Constructor::new()).into_port(names_iter);
    let bot_rhs: Port = Expr::Constr(Constructor::new()).into_port(names_iter);

    let top_lhs: Port = Expr::Dup(Duplicator::new()).into_port(names_iter);
    let top_rhs: Port = Expr::Dup(Duplicator::new()).into_port(names_iter);

    top_lhs
        .borrow_mut()
        .set_aux_ports([Some((1, bot_rhs.clone())), Some((1, bot_lhs.clone()))]);
    top_rhs
        .borrow_mut()
        .set_aux_ports([Some((2, bot_rhs.clone())), Some((2, bot_lhs.clone()))]);
    bot_lhs
        .borrow_mut()
        .set_aux_ports([Some((2, top_lhs.clone())), Some((2, top_rhs.clone()))]);
    bot_rhs
        .borrow_mut()
        .set_aux_ports([Some((1, top_lhs.clone())), Some((1, top_rhs.clone()))]);

    // Connect original top left, top right, bottom left, bottom right vars
    // to new agents
    match &original_ports {
        [a, b, c, d] => {
            top_lhs.borrow_mut().set_primary_port(a.clone());
            top_rhs.borrow_mut().set_primary_port(b.clone());
            bot_lhs.borrow_mut().set_primary_port(d.clone());
            bot_rhs.borrow_mut().set_primary_port(c.clone());
        }
    }

    if let Some((p, top_left)) = &original_ports[0] {
        top_left
            .borrow_mut()
            .swap_conn(*p, Some((0, top_lhs.clone())));
    }

    if let Some((p, top_right)) = &original_ports[1] {
        top_right
            .borrow_mut()
            .swap_conn(*p, Some((0, top_rhs.clone())));
    }

    if let Some((p, bot_left)) = &original_ports[2] {
        bot_left
            .borrow_mut()
            .swap_conn(*p, Some((0, bot_rhs.clone())));
    }

    if let Some((p, bot_right)) = &original_ports[3] {
        bot_right
            .borrow_mut()
            .swap_conn(*p, Some((0, bot_lhs.clone())));
    }

    Some(vec![top_lhs])
}

fn make_constr_era_commutation_net(
    original_ports: [Option<IndexedPort>; 2],
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

    if let Some((p, top_left)) = &original_ports[0] {
        top_left
            .borrow_mut()
            .swap_conn(*p, Some((0, era_lhs.clone())));
    }

    if let Some((p, top_right)) = &original_ports[1] {
        top_right
            .borrow_mut()
            .swap_conn(*p, Some((0, era_rhs.clone())));
    }

    Some(vec![era_lhs, era_rhs])
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::parser::parser_combinators as parser;
    use chumsky::Parser;

    #[test_log::test]
    fn test_reduce() {
        let cases = [
            (
                "Constr[@1](a, b) >< Constr[@2](c, d)",
                vec!["a ~ c", "b ~ d"],
            ),
            ("Dup[@1](a, b) >< Dup[@2](c, d)", vec!["a ~ c", "b ~ d"]),
            ("Era[@1]() >< Era[@2]()", vec![]),
            (
                "Constr[@1](a, b) >< Era[@2]()",
                vec!["Era[@0](a)", "Era[@1](b)"],
            ),
            (
                "Dup[@1](a, b) >< Era[@2]()",
                vec!["Era[@0](a)", "Era[@1](b)"],
            ),
            (
                "Constr[@1](a, b) >< Dup[@2](d, c)",
                vec!["Dup[@2](a, Constr[@1](d, @2, Dup[@3](b, @1, Constr[@0](c, @2, @3))), @0)"],
            ),
            (
                "Dup[@1](a, b) >< Constr[@2](d, c)",
                vec!["Constr[@2](a, Dup[@1](d, @2, Constr[@3](b, @1, Dup[@0](c, @2, @3))), @0)"],
            ),
        ];

        for (case, expected) in cases {
            let parsed = parser::parser()
                .parse(parser::lexer().parse(case).unwrap())
                .unwrap();

            assert_eq!(
                reduce_dyn(&parsed[0].0)
                    .unwrap()
                    .iter()
                    .map(|x| x.to_string())
                    .collect::<Vec<_>>(),
                expected.iter().map(|x| x.as_ref()).collect::<Vec<_>>(),
            );
        }
    }
}
