use crate::parser::{
    ast_combinators::{Constructor, Duplicator, Eraser, Expr, IndexedPort, Port},
    naming::NameIter,
};
use std::{collections::BTreeSet, sync::Arc};

#[cfg(feature = "threadpool")]
use rayon::prelude::*;

#[derive(Default, Debug, Clone)]
pub struct Reduction {
    pub nets: Vec<Port>,
    pub active_pairs: Vec<Port>,
}

#[cfg(feature = "threadpool")]
pub fn reduce_dyn(e: &Port) -> Vec<Port> {
    let mut redex_bag = e
        .iter_tree()
        .filter(|x| x.try_as_active_pair().is_some())
        .collect::<Vec<_>>();
    let mut nets = BTreeSet::new();
    let names = Arc::new(NameIter::default());

    while !redex_bag.is_empty() {
        let Reduction {
            active_pairs: c_active_pairs,
            nets: c_nets,
        } = redex_bag
            .par_drain(..)
            .filter_map(|x| reduce_step_dyn(&x, names.clone()))
            .reduce(
                || Reduction::default(),
                |mut acc, res| {
                    let Reduction { nets, active_pairs } = res;

                    acc.nets.extend(nets);
                    acc.active_pairs.extend(active_pairs);

                    acc
                },
            );

        nets.extend(c_nets.into_iter().map(|x| x.orient()));
        redex_bag.extend(c_active_pairs);
    }

    nets.into_iter().collect()
}

#[cfg(not(feature = "threadpool"))]
pub fn reduce_dyn(e: &Port) -> Vec<Port> {
    let mut redex_bag = e
        .iter_tree()
        .filter(|x| x.try_as_active_pair().is_some())
        .collect::<Vec<_>>();
    let mut nets = BTreeSet::new();
    let names = Arc::new(NameIter::default());

    while !redex_bag.is_empty() {
        let Reduction {
            active_pairs: c_active_pairs,
            nets: c_nets,
        } = redex_bag
            .drain(..)
            .filter_map(|x| reduce_step_dyn(&x, names.clone()))
            .fold(Reduction::default(), |mut acc, res| {
                let Reduction { nets, active_pairs } = res;

                acc.nets.extend(nets);
                acc.active_pairs.extend(active_pairs);

                acc
            });

        nets.extend(c_nets.into_iter().map(|x| x.orient()));
        redex_bag.extend(c_active_pairs);
    }

    nets.into_iter().collect()
}

pub fn reduce_step_dyn(e: &Port, names: Arc<NameIter>) -> Option<Reduction> {
    let (e, e2) = if let Some(active_pair) = e.try_as_active_pair() {
        active_pair
    } else {
        return None;
    };

    let mut redexes = Vec::new();

    let (lhs, rhs) = { (e.1.borrow().clone(), e2.1.borrow().clone()) };

    let mut connect = |p: &Port, idx: usize, val: Option<(usize, Port)>| {
        // New redex!
        if val.as_ref().map(|v| v.0) == Some(0) && idx == 0 {
            redexes.push(p.clone());
        }

        if let Some((port, px)) = val.clone() {
            px.borrow_mut().swap_conn(port, Some((idx, p.clone())));
        }

        p.borrow_mut().swap_conn(idx, val);
    };

    let nets = match (lhs, rhs) {
        // commutation of constr >< dup
        (Expr::Constr(ref c), Expr::Dup(ref d)) => {
            let original_ports = [
                c.aux_ports[0].clone(),
                c.aux_ports[1].clone(),
                d.aux_ports[1].clone(),
                d.aux_ports[0].clone(),
            ];

            make_constr_dup_commutation_net(original_ports, names, connect)
        }
        (Expr::Dup(ref c), Expr::Constr(ref d)) => {
            let original_ports = [
                c.aux_ports[0].clone(),
                c.aux_ports[1].clone(),
                d.aux_ports[1].clone(),
                d.aux_ports[0].clone(),
            ];

            make_dup_constr_commutation_net(original_ports, names, connect)
        }
        // commutation of constr >< era
        (Expr::Constr(ref c), Expr::Era(_)) => {
            let original_ports = [c.aux_ports[0].clone(), c.aux_ports[1].clone()];

            make_constr_era_commutation_net(original_ports, names, connect)
        }
        (Expr::Era(_), Expr::Constr(ref c)) => {
            let original_ports = [c.aux_ports[0].clone(), c.aux_ports[1].clone()];

            make_constr_era_commutation_net(original_ports, names, connect)
        }
        // Commutation of dup >< era
        (Expr::Dup(ref c), Expr::Era(_)) => {
            let original_ports = [c.aux_ports[0].clone(), c.aux_ports[1].clone()];

            make_constr_era_commutation_net(original_ports, names, connect)
        }
        (Expr::Era(_), Expr::Dup(ref c)) => {
            let original_ports = [c.aux_ports[0].clone(), c.aux_ports[1].clone()];

            make_constr_era_commutation_net(original_ports, names, connect)
        }
        // Annihiliation of Constr
        (Expr::Constr(ref c), Expr::Constr(ref d)) => {
            let original_ports = [
                c.aux_ports[0].clone(),
                d.aux_ports[0].clone(),
                c.aux_ports[1].clone(),
                d.aux_ports[1].clone(),
            ];

            if let Some((port, p)) = original_ports[0].as_ref() {
                connect(p, *port, original_ports[1].clone());
            }
            if let Some((port, p)) = original_ports[1].as_ref() {
                connect(p, *port, original_ports[0].clone());
            }
            if let Some((port, p)) = original_ports[2].as_ref() {
                connect(p, *port, original_ports[3].clone());
            }
            if let Some((port, p)) = original_ports[3].as_ref() {
                connect(p, *port, original_ports[2].clone());
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
                connect(p, *port, original_ports[1].clone());
            }
            if let Some((port, p)) = original_ports[1].as_ref() {
                connect(p, *port, original_ports[0].clone());
            }
            if let Some((port, p)) = original_ports[2].as_ref() {
                connect(p, *port, original_ports[3].clone());
            }
            if let Some((port, p)) = original_ports[3].as_ref() {
                connect(p, *port, original_ports[2].clone());
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
        (Expr::Era(_), Expr::Era(_)) => Some(vec![]),
        // No rule for vars
        _ => None,
    };

    Some(Reduction {
        nets: nets?,
        active_pairs: redexes,
    })
}

// TODO: do this with adjacency matrix, perhaps
// for a single owner, no refcell necessary
fn make_dup_constr_commutation_net(
    original_ports: [Option<IndexedPort>; 4],
    names_iter: Arc<NameIter>,
    mut connect: impl FnMut(&Port, usize, Option<(usize, Port)>),
) -> Option<Vec<Port>> {
    let bot_lhs: Port = Expr::Dup(Duplicator::new()).into_port(&names_iter);
    let bot_rhs: Port = Expr::Dup(Duplicator::new()).into_port(&names_iter);

    let top_lhs: Port = Expr::Constr(Constructor::new()).into_port(&names_iter);
    let top_rhs: Port = Expr::Constr(Constructor::new()).into_port(&names_iter);

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
            bot_lhs.borrow_mut().set_primary_port(c.clone());
            bot_rhs.borrow_mut().set_primary_port(d.clone());
        }
    }

    if let Some((p, top_left)) = &original_ports[0] {
        connect(top_left, *p, Some((0, top_lhs.clone())));
    }

    if let Some((p, top_right)) = &original_ports[1] {
        connect(top_right, *p, Some((0, top_rhs.clone())));
    }

    if let Some((p, bot_left)) = &original_ports[2] {
        connect(bot_left, *p, Some((0, bot_lhs.clone())));
    }

    if let Some((p, bot_right)) = &original_ports[3] {
        connect(bot_right, *p, Some((0, bot_rhs.clone())));
    }

    Some(vec![top_lhs])
}

fn make_constr_dup_commutation_net(
    original_ports: [Option<IndexedPort>; 4],
    names_iter: Arc<NameIter>,
    mut connect: impl FnMut(&Port, usize, Option<(usize, Port)>),
) -> Option<Vec<Port>> {
    let bot_lhs: Port = Expr::Constr(Constructor::new()).into_port(&names_iter);
    let bot_rhs: Port = Expr::Constr(Constructor::new()).into_port(&names_iter);

    let top_lhs: Port = Expr::Dup(Duplicator::new()).into_port(&names_iter);
    let top_rhs: Port = Expr::Dup(Duplicator::new()).into_port(&names_iter);

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
            bot_lhs.borrow_mut().set_primary_port(c.clone());
            bot_rhs.borrow_mut().set_primary_port(d.clone());
        }
    }

    if let Some((p, top_left)) = &original_ports[0] {
        connect(top_left, *p, Some((0, top_lhs.clone())));
    }

    if let Some((p, top_right)) = &original_ports[1] {
        connect(top_right, *p, Some((0, top_rhs.clone())));
    }

    if let Some((p, bot_left)) = &original_ports[2] {
        connect(bot_left, *p, Some((0, bot_lhs.clone())));
    }

    if let Some((p, bot_right)) = &original_ports[3] {
        connect(bot_right, *p, Some((0, bot_rhs.clone())));
    }

    Some(vec![top_lhs])
}

fn make_constr_era_commutation_net(
    original_ports: [Option<IndexedPort>; 2],
    names_iter: Arc<NameIter>,
    mut connect: impl FnMut(&Port, usize, Option<(usize, Port)>),
) -> Option<Vec<Port>> {
    let era_lhs: Port = Expr::Era(Eraser::new()).into_port(&names_iter);
    let era_rhs: Port = Expr::Era(Eraser::new()).into_port(&names_iter);

    era_lhs
        .borrow_mut()
        .set_primary_port(original_ports[0].clone());
    era_rhs
        .borrow_mut()
        .set_primary_port(original_ports[1].clone());

    if let Some((p, top_left)) = &original_ports[0] {
        connect(top_left, *p, Some((0, era_lhs.clone())));
    }

    if let Some((p, top_right)) = &original_ports[1] {
        connect(top_right, *p, Some((0, era_rhs.clone())));
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
                BTreeSet::from_iter(["c ~ a", "d ~ b"]),
            ),
            ("Dup[@1](a, b) >< Dup[@2](c, d)", BTreeSet::from_iter(["c ~ a", "d ~ b"])),
            ("Era[@1]() >< Era[@2]()", BTreeSet::from_iter([])),
            (
                "Constr[@1](a, b) >< Era[@2]()",
                BTreeSet::from_iter(["Era[@2](a)", "Era[@3](b)"]),
            ),
            (
                "Dup[@1](a, b) >< Era[@2]()",
                BTreeSet::from_iter(["Era[@2](a)", "Era[@3](b)"]),
            ),
            (
                "Constr[@1](a, b) >< Dup[@2](d, c)",
                BTreeSet::from_iter(["Dup[@5](a, Constr[@6](d, @5#1, Dup[@4](b, @6#2, Constr[@7](c, @5#2, @4#2)#2)#1)#1, @7#1)"]),
            ),
            (
                "Dup[@1](a, b) >< Constr[@2](d, c)",
                BTreeSet::from_iter(["Constr[@5](a, Dup[@6](d, @5#1, Constr[@4](b, @6#2, Dup[@7](c, @5#2, @4#2)#2)#1)#1, @7#1)"]),
            ),
        ];

        for (case, expected) in cases {
            println!("{}", case);
            let parsed = parser::parser()
                .parse(parser::lexer().parse(case).unwrap())
                .unwrap();

            let res = reduce_dyn(&parsed[0].0);

            assert_eq!(
                res.iter().map(|x| x.to_string()).collect::<BTreeSet<_>>(),
                expected
                    .iter()
                    .map(|x| x.to_string())
                    .collect::<BTreeSet<_>>(),
            );
        }
    }
}
