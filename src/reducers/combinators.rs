use crate::parser::ast_combinators::{Constructor, Duplicator, Eraser, Expr, Port};
use std::{cell::RefCell, rc::Rc};

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
            .swap_conn(&lhs, top_lhs.clone());
    }

    if let Some(top_right) = &original_ports[1] {
        top_right
            .try_borrow_mut()
            .ok()?
            .swap_conn(&lhs, top_rhs.clone());
    }

    if let Some(bot_left) = &original_ports[2] {
        bot_left
            .try_borrow_mut()
            .ok()?
            .swap_conn(&rhs, bot_lhs.clone());
    }

    if let Some(bot_right) = &original_ports[3] {
        bot_right
            .try_borrow_mut()
            .ok()?
            .swap_conn(&rhs, bot_rhs.clone());
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
            .swap_conn(&lhs, era_lhs.clone());
    }

    if let Some(top_right) = &original_ports[1] {
        top_right
            .try_borrow_mut()
            .ok()?
            .swap_conn(&lhs, era_rhs.clone());
    }

    Some(vec![era_lhs, era_rhs])
}

pub fn reduce_dyn(e: Port) -> Option<Vec<Rc<RefCell<Expr>>>> {
    let e_borrow = e.as_ref().try_borrow_mut().ok()?;
    let (lhs, rhs) = e_borrow.try_as_active_pair()?;
    let e2_borrow = e.as_ref().try_borrow().ok()?;
    let e2 = e2_borrow.primary_port()?;

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
                c.aux_ports[0].clone()?,
                d.aux_ports[0].clone()?,
                c.aux_ports[1].clone()?,
                d.aux_ports[1].clone()?,
            ];

            original_ports[0]
                .try_borrow_mut()
                .ok()?
                .swap_conn(&e, original_ports[1].clone());
            original_ports[1]
                .try_borrow_mut()
                .ok()?
                .swap_conn(&e2, original_ports[0].clone());
            original_ports[2]
                .try_borrow_mut()
                .ok()?
                .swap_conn(&e, original_ports[2].clone());
            original_ports[2]
                .try_borrow_mut()
                .ok()?
                .swap_conn(&e2, original_ports[3].clone());

            Some(original_ports.into_iter().collect())
        }
        // Anihilation of dupl
        (&Expr::Dup(ref c), &Expr::Dup(ref d)) => {
            let original_ports = [
                c.aux_ports[0].clone()?,
                d.aux_ports[1].clone()?,
                c.aux_ports[1].clone()?,
                d.aux_ports[0].clone()?,
            ];

            original_ports[0]
                .try_borrow_mut()
                .ok()?
                .swap_conn(&e, original_ports[1].clone());
            original_ports[1]
                .try_borrow_mut()
                .ok()?
                .swap_conn(&e2, original_ports[0].clone());
            original_ports[2]
                .try_borrow_mut()
                .ok()?
                .swap_conn(&e, original_ports[2].clone());
            original_ports[2]
                .try_borrow_mut()
                .ok()?
                .swap_conn(&e2, original_ports[3].clone());

            Some(original_ports.into_iter().collect())
        }
        // Anihilation of era
        (&Expr::Era(_), &Expr::Era(_)) => Some(Vec::new()),
        // No rule for vars
        _ => None,
    }
}
