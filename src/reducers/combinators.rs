use crate::parser::ast_combinators::{
    try_as_active_pair, Constructor, Duplicator, Eraser, Expr, Port,
};

pub fn reduce_dyn(e: Port) -> Option<Vec<Port>> {
    let (e, e2) = try_as_active_pair(&e)?;
    let (lhs, rhs) = (e.try_borrow().ok()?, e2.try_borrow().ok()?);

    match (&*lhs, &*rhs) {
        // commutation of constr >< dup
        (&Expr::Constr(ref c), &Expr::Dup(ref d)) => {
            let original_ports = [
                c.aux_ports[0].clone(),
                c.aux_ports[1].clone(),
                d.aux_ports[0].clone(),
                d.aux_ports[1].clone(),
            ];

            make_constr_dup_commutation_net(original_ports, e.clone(), e2.clone())
        }
        (&Expr::Dup(ref d), &Expr::Constr(ref c)) => {
            let original_ports = [
                c.aux_ports[0].clone(),
                c.aux_ports[1].clone(),
                d.aux_ports[0].clone(),
                d.aux_ports[1].clone(),
            ];

            make_constr_dup_commutation_net(original_ports, e2.clone(), e.clone())
        }
        // commutation of constr >< era
        (&Expr::Constr(ref c), &Expr::Era(_)) => {
            let original_ports = [c.aux_ports[0].clone(), c.aux_ports[1].clone()];

            make_constr_era_commutation_net(original_ports, e.clone())
        }
        (&Expr::Era(_), &Expr::Constr(ref c)) => {
            let original_ports = [c.aux_ports[0].clone(), c.aux_ports[1].clone()];

            make_constr_era_commutation_net(original_ports, e2.clone())
        }
        // Commutation of dup >< era
        (&Expr::Dup(ref c), &Expr::Era(_)) => {
            let original_ports = [c.aux_ports[0].clone(), c.aux_ports[1].clone()];

            make_constr_era_commutation_net(original_ports, e.clone())
        }
        (&Expr::Era(_), &Expr::Dup(ref c)) => {
            let original_ports = [c.aux_ports[0].clone(), c.aux_ports[1].clone()];

            make_constr_era_commutation_net(original_ports, e2.clone())
        }
        // Annihiliation of Constr
        (&Expr::Constr(ref c), &Expr::Constr(ref d)) => {
            let original_ports = [
                c.aux_ports[0].clone(),
                d.aux_ports[0].clone(),
                c.aux_ports[1].clone(),
                d.aux_ports[1].clone(),
            ];

            if let Some(p) = original_ports[0].as_ref() {
                p.try_borrow_mut()
                    .ok()?
                    .swap_conn(&e, original_ports[1].clone());
            }
            if let Some(p) = original_ports[1].as_ref() {
                p.try_borrow_mut()
                    .ok()?
                    .swap_conn(&e2, original_ports[0].clone());
            }
            if let Some(p) = original_ports[2].as_ref() {
                p.try_borrow_mut()
                    .ok()?
                    .swap_conn(&e, original_ports[2].clone());
            }
            if let Some(p) = original_ports[2].as_ref() {
                p.try_borrow_mut()
                    .ok()?
                    .swap_conn(&e2, original_ports[3].clone());
            }

            Some(original_ports.into_iter().filter_map(|x| x).collect())
        }
        // Anihilation of dupl
        (&Expr::Dup(ref c), &Expr::Dup(ref d)) => {
            let original_ports = [
                c.aux_ports[0].clone(),
                d.aux_ports[1].clone(),
                c.aux_ports[1].clone(),
                d.aux_ports[0].clone(),
            ];

            if let Some(p) = original_ports[0].as_ref() {
                p.try_borrow_mut()
                    .ok()?
                    .swap_conn(&e, original_ports[1].clone());
            }
            if let Some(p) = original_ports[1].as_ref() {
                p.try_borrow_mut()
                    .ok()?
                    .swap_conn(&e2, original_ports[0].clone());
            }
            if let Some(p) = original_ports[2].as_ref() {
                p.try_borrow_mut()
                    .ok()?
                    .swap_conn(&e, original_ports[2].clone());
            }
            if let Some(p) = original_ports[2].as_ref() {
                p.try_borrow_mut()
                    .ok()?
                    .swap_conn(&e2, original_ports[3].clone());
            }

            Some(original_ports.into_iter().filter_map(|x| x).collect())
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
) -> Option<Vec<Port>> {
    let top_lhs: Port = Expr::Dup(Duplicator::new()).into();
    let top_rhs: Port = Expr::Dup(Duplicator::new()).into();

    let bot_lhs: Port = Expr::Constr(Constructor::new()).into();
    let bot_rhs: Port = Expr::Constr(Constructor::new()).into();

    top_lhs
        .try_borrow_mut()
        .ok()?
        .set_aux_ports([Some(bot_lhs.clone()), Some(bot_rhs.clone())]);
    top_rhs
        .try_borrow_mut()
        .ok()?
        .set_aux_ports([Some(bot_lhs.clone()), Some(bot_rhs.clone())]);
    bot_lhs
        .try_borrow_mut()
        .ok()?
        .set_aux_ports([Some(top_lhs.clone()), Some(top_rhs.clone())]);
    bot_rhs
        .try_borrow_mut()
        .ok()?
        .set_aux_ports([Some(top_lhs.clone()), Some(top_rhs.clone())]);

    // Connect original top left, top right, bottom left, bottom right vars
    // to new agents
    match &original_ports {
        [a, b, c, d] => {
            top_lhs.try_borrow_mut().ok()?.set_primary_port(a.clone());
            top_rhs.try_borrow_mut().ok()?.set_primary_port(b.clone());
            bot_lhs.try_borrow_mut().ok()?.set_primary_port(c.clone());
            bot_rhs.try_borrow_mut().ok()?.set_primary_port(d.clone());
        }
    }

    if let Some(top_left) = &original_ports[0] {
        top_left
            .try_borrow_mut()
            .ok()?
            .swap_conn(&lhs, Some(top_lhs.clone()));
    }

    if let Some(top_right) = &original_ports[1] {
        top_right
            .try_borrow_mut()
            .ok()?
            .swap_conn(&lhs, Some(top_rhs.clone()));
    }

    if let Some(bot_left) = &original_ports[2] {
        bot_left
            .try_borrow_mut()
            .ok()?
            .swap_conn(&rhs, Some(bot_lhs.clone()));
    }

    if let Some(bot_right) = &original_ports[3] {
        bot_right
            .try_borrow_mut()
            .ok()?
            .swap_conn(&rhs, Some(bot_rhs.clone()));
    }

    Some(vec![top_lhs])
}

fn make_constr_era_commutation_net(
    original_ports: [Option<Port>; 2],
    lhs: Port,
) -> Option<Vec<Port>> {
    let era_lhs: Port = Expr::Era(Eraser::new()).into();
    let era_rhs: Port = Expr::Era(Eraser::new()).into();

    era_lhs
        .try_borrow_mut()
        .ok()?
        .set_primary_port(original_ports[0].clone());
    era_rhs
        .try_borrow_mut()
        .ok()?
        .set_primary_port(original_ports[1].clone());

    if let Some(top_left) = &original_ports[0] {
        top_left
            .try_borrow_mut()
            .ok()?
            .swap_conn(&lhs, Some(era_lhs.clone()));
    }

    if let Some(top_right) = &original_ports[1] {
        top_right
            .try_borrow_mut()
            .ok()?
            .swap_conn(&lhs, Some(era_rhs.clone()));
    }

    Some(vec![era_lhs, era_rhs])
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_reduce_commute_dup_constr() {
        let top: Port = Expr::Constr(Constructor::new()).into();
        let bottom: Port = Expr::Dup(Duplicator::new()).into();

        top.borrow_mut().set_primary_port(Some(bottom.clone()));
        bottom.borrow_mut().set_primary_port(Some(top.clone()));

        let res = reduce_dyn(top);
        assert!(res.is_some());
    }

    #[test]
    fn test_reduce_commute_dup_era() {
        let top: Port = Expr::Dup(Duplicator::new()).into();
        let bottom: Port = Expr::Era(Eraser::new()).into();

        top.borrow_mut().set_primary_port(Some(bottom.clone()));
        bottom.borrow_mut().set_primary_port(Some(top.clone()));

        let res = reduce_dyn(top);
        assert!(res.is_some());
    }

    #[test]
    fn test_reduce_commute_constr_era() {
        let top: Port = Expr::Constr(Constructor::new()).into();
        let bottom: Port = Expr::Era(Eraser::new()).into();

        top.borrow_mut().set_primary_port(Some(bottom.clone()));
        bottom.borrow_mut().set_primary_port(Some(top.clone()));

        let res = reduce_dyn(top);
        assert!(res.is_some());
    }

    #[test]
    fn test_reduce_annihilate_constr_constr() {
        let top: Port = Expr::Constr(Constructor::new()).into();
        let bottom: Port = Expr::Constr(Constructor::new()).into();

        top.borrow_mut().set_primary_port(Some(bottom.clone()));
        bottom.borrow_mut().set_primary_port(Some(top.clone()));

        let res = reduce_dyn(top);
        assert!(res.is_some());
    }

    #[test]
    fn test_reduce_annihilate_dup_dup() {
        let top: Port = Expr::Dup(Duplicator::new()).into();
        let bottom: Port = Expr::Dup(Duplicator::new()).into();

        top.borrow_mut().set_primary_port(Some(bottom.clone()));
        bottom.borrow_mut().set_primary_port(Some(top.clone()));

        let res = reduce_dyn(top);
        assert!(res.is_some());
    }

    #[test]
    fn test_reduce_annihilate_era_era() {
        let top: Port = Expr::Era(Eraser::new()).into();
        let bottom: Port = Expr::Era(Eraser::new()).into();

        top.borrow_mut().set_primary_port(Some(bottom.clone()));
        bottom.borrow_mut().set_primary_port(Some(top.clone()));

        let res = reduce_dyn(top);
        assert!(res.unwrap().is_empty());
    }
}
