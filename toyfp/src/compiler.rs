use super::parser::Expr;
use inetlib::parser::{
    ast_combinators::{self as ast_icc, Constructor, Duplicator, Eraser, Port, Var},
    ast_lafont::Ident,
    naming::NameIter,
    parser_combinators,
};

pub fn compile(e: Expr, names: &mut NameIter) -> Port {
    match e {
        Expr::Id(i) => ast_icc::Expr::Var(Var {
            name: Ident(i),
            port: None,
        })
        .into_port(names),
        Expr::Abstraction { body, .. } => {
            let p = ast_icc::Expr::Constr(Constructor::new()).into_port(names);
            let body = compile(*body, names);
            let ret_var = ast_icc::Expr::Var(Var {
                name: Ident(format!("ret#{}", names.next())),
                port: Some(p.clone()),
            })
            .into_port(names);

            p.borrow_mut().set_aux_ports([Some(ret_var), Some(body)]);

            p
        }
        Expr::Application { lhs, rhs } => {
            let (bind_id, body) = if let Expr::Abstraction { bind_id, body } = *lhs {
                (bind_id, body)
            } else {
                unimplemented!()
            };

            let body_net = compile(*body, names);
            let arg_net = compile(*rhs, names);

            let lam_net = ast_icc::Expr::Constr(Constructor::new()).into_port(names);
            let app_net = ast_icc::Expr::Constr(Constructor::new()).into_port(names);

            lam_net.borrow_mut().set_primary_port(Some(app_net.clone()));
            app_net.borrow_mut().set_primary_port(Some(lam_net.clone()));

            // Typing
            let bind_id_var = ast_icc::Expr::Var(Var {
                name: Ident(bind_id),
                port: Some(app_net.clone()),
            })
            .into_port(names);
            let body_id_var = body_net.clone();

            lam_net
                .borrow_mut()
                .set_aux_ports([None, Some(body_id_var)]);
            app_net
                .borrow_mut()
                .set_aux_ports([Some(bind_id_var), None]);

            // Implementation
            // TODO: How do we handle successive calls?
            // need to nest more agents here
            let ret_var = ast_icc::Expr::Var(Var {
                name: Ident(format!("ret#{}", names.next())),
                port: Some(lam_net.clone()),
            })
            .into_port(names);

            app_net.borrow_mut().push_aux_port(Some(arg_net));
            lam_net.borrow_mut().push_aux_port(Some(ret_var));

            lam_net
        }
    }
}

pub fn decompile(p: &Port) -> Option<Expr> {
    // There should be no active pairs left at this stage, since reduction
    // is done

    // Remaining constr is an abstraction, anything else is just a var
    match &*p.borrow() {
        ast_icc::Expr::Constr(c) => {
            unimplemented!()
        }
        // Lone vars are just vars
        ast_icc::Expr::Var(v) => {
            // Anything in ret position is a result
            if let Some(ret) = &v.port {
                if let Some(v) = ret.borrow().as_var() {
                    Some(Expr::Id(v.name.0.clone()))
                } else {
                    decompile(&p)
                }
            } else {
                Some(Expr::Id(v.name.0.clone()))
            }
        }
        _ => None,
    }
}

pub fn make_z_comb(i: usize, names: &mut NameIter) -> Port {
    use chumsky::prelude::*;

    match i {
        0 => {
            // Unwrap is fine here, since we are hard coding the values
            // Todo: make a compile time proc macro for this?
            parser_combinators::parser()
                .parse(
                    parser_combinators::lexer()
                        .parse(format!(
                            "Era[@{}]({})",
                            names.next_id(),
                            names.next_var_name()
                        ))
                        .unwrap(),
                )
                .unwrap()
                .remove(0)
                .0
        }
        1 => {
            parser_combinators::parser()
                .parse(
                    parser_combinators::lexer()
                        .parse(format!(
                            "{} ~ {}",
                            names.next_var_name(),
                            names.next_var_name()
                        ))
                        .unwrap(),
                )
                .unwrap()
                .remove(0)
                .0
        }
        n => {
            let prev = make_z_comb(n - 1, names);
            let child = ast_icc::Expr::Constr(Constructor::new()).into_port(names);
            let var_top = ast_icc::Expr::Var(Var {
                name: Ident(names.next_var_name()),
                port: Some(child.clone()),
            })
            .into_port(names);
            let var_bottom = ast_icc::Expr::Var(Var {
                name: Ident(names.next_var_name()),
                port: Some(child.clone()),
            })
            .into_port(names);

            child
                .borrow_mut()
                .set_aux_ports([Some(prev.clone()), Some(var_top)]);
            child.borrow_mut().set_primary_port(Some(var_bottom));
            prev.borrow_mut().set_primary_port(Some(child.clone()));

            child
        }
    }
}

pub fn make_d_comb(names: &mut NameIter) -> Port {
    let z = make_z_comb(4, names);

    // Insert a dup connected to first two left ports
    let dup = ast_icc::Expr::Dup(Duplicator::new()).into_port(names);

    // This should not fail
    let aux_port_port_3 = z.borrow().aux_ports()[0].clone().unwrap();
    let aux_port_port_2 = aux_port_port_3.borrow().aux_ports()[0].clone().unwrap();

    dup.borrow_mut()
        .set_primary_port(Some(aux_port_port_3.clone()));
    aux_port_port_3.borrow_mut().push_aux_port(Some(z.clone()));
    dup.borrow_mut()
        .set_aux_ports([Some(aux_port_port_2.clone()), Some(aux_port_port_2.clone())]);

    aux_port_port_2
        .borrow_mut()
        .set_aux_ports([Some(dup.clone()), Some(dup.clone())]);
    aux_port_port_3
        .borrow_mut()
        .push_aux_port(Some(dup.clone()));

    z
}

pub fn make_k_comb(names: &mut NameIter) -> Port {
    let z = make_z_comb(3, names);
    let d = make_d_comb(names);

    // This should not fail
    let aux_port_port = z.borrow().aux_ports()[0].clone().unwrap();

    d.borrow_mut().push_aux_port(Some(aux_port_port.clone()));
    d.borrow_mut().set_primary_port(Some(z.clone()));

    let era = ast_icc::Expr::Era(Eraser::new()).into_port(names);
    era.borrow_mut()
        .set_primary_port(Some(aux_port_port.clone()));

    aux_port_port
        .borrow_mut()
        .set_aux_ports([Some(d.clone()), Some(era.clone())]);

    z.borrow_mut().push_aux_port(Some(d.clone()));

    z
}

/// Inserts in the specified port index in the Z agent
fn insert_z_4_aux_port(z: &Port, i: usize, val: Port) -> Option<Port> {
    let aux_port_port_3 = z.borrow().aux_ports()[0].clone().unwrap();
    let aux_port_port_2 = aux_port_port_3.borrow().aux_ports()[0].clone().unwrap();

    match i {
        0 => {
            aux_port_port_2.borrow_mut().push_aux_port(Some(val));

            Some(aux_port_port_2)
        }
        1 => {
            aux_port_port_2.borrow_mut().push_aux_port(Some(val));

            Some(aux_port_port_2)
        }
        2 => {
            aux_port_port_2.borrow_mut().push_aux_port(Some(val));

            Some(aux_port_port_3)
        }
        3 => {
            z.borrow_mut().push_aux_port(Some(val));

            Some(z.clone())
        }
        _ => None,
    }
}

/// Returns the port which the value was inserted into.
/// Pushes into the next port with no value
fn push_z_4_aux_port(z: &Port, val: Port) -> Port {
    let aux_port_port_3 = z.borrow().aux_ports()[0].clone().unwrap();
    let aux_port_port_2 = aux_port_port_3.borrow().aux_ports()[0].clone().unwrap();

    if aux_port_port_2.borrow().aux_ports()[0]
        .as_ref()
        .map(|p| p.borrow().is_var())
        .unwrap_or_default()
    {
        aux_port_port_2.borrow_mut().push_aux_port(Some(val));

        aux_port_port_2
    } else if aux_port_port_2.borrow().aux_ports()[1]
        .as_ref()
        .map(|p| p.borrow().is_var())
        .unwrap_or_default()
    {
        aux_port_port_2.borrow_mut().push_aux_port(Some(val));

        aux_port_port_2
    } else if aux_port_port_3.borrow().aux_ports()[1]
        .as_ref()
        .map(|p| p.borrow().is_var())
        .unwrap_or_default()
    {
        aux_port_port_2.borrow_mut().push_aux_port(Some(val));

        aux_port_port_3
    } else {
        z.borrow_mut().push_aux_port(Some(val));

        z.clone()
    }
}

pub fn nth_z_4_aux_Port(z: &Port, i: usize) -> Option<Port> {
    let aux_port_port_3 = z.borrow().aux_ports()[0].clone().unwrap();
    let aux_port_port_2 = aux_port_port_3.borrow().aux_ports()[0].clone().unwrap();

    match i {
        0 => Some(aux_port_port_2),
        1 => Some(aux_port_port_2),
        2 => Some(aux_port_port_3),
        3 => Some(z.clone()),
        _ => None,
    }
}

pub fn make_s_comb(names: &mut NameIter) -> Port {
    let z_bottom_right = make_z_comb(4, names);

    let z_top_left = make_z_comb(4, names);
    let constr_left_z_bottom = ast_icc::Expr::Constr(Constructor::new()).into_port(names);
    let dup_middle_z_bottom = ast_icc::Expr::Dup(Duplicator::new()).into_port(names);
    let d_right_z_bottom = make_d_comb(names);

    let cl = constr_left_z_bottom.clone();
    constr_left_z_bottom
        .borrow_mut()
        .set_aux_ports([None, Some(push_z_4_aux_port(&z_bottom_right, cl))]);
    let dz = dup_middle_z_bottom.clone();
    dup_middle_z_bottom
        .borrow_mut()
        .set_primary_port(Some(push_z_4_aux_port(&z_bottom_right, dz)));
    z_top_left
        .borrow_mut()
        .set_primary_port(Some(push_z_4_aux_port(&z_bottom_right, z_top_left.clone())));
    d_right_z_bottom
        .borrow_mut()
        .set_primary_port(Some(push_z_4_aux_port(
            &z_bottom_right,
            d_right_z_bottom.clone(),
        )));

    let d_constr = ast_icc::Expr::Constr(Constructor::new()).into_port(names);
    d_right_z_bottom
        .borrow_mut()
        .push_aux_port(Some(d_constr.clone()));
    d_constr
        .borrow_mut()
        .set_primary_port(Some(d_right_z_bottom.clone()));

    let d_sub_constr = constr_left_z_bottom;
    d_constr.borrow_mut().set_aux_ports([
        Some(dup_middle_z_bottom.clone()),
        Some(d_sub_constr.clone()),
    ]);
    d_sub_constr
        .borrow_mut()
        .set_primary_port(Some(d_constr.clone()));

    let z_middle = make_z_comb(4, names);
    z_middle
        .borrow_mut()
        .set_primary_port(Some(d_sub_constr.clone()));
    d_sub_constr
        .borrow_mut()
        .set_aux_ports([Some(z_middle.clone()), Some(z_bottom_right.clone())]);

    let middle_constr = ast_icc::Expr::Constr(Constructor::new()).into_port(names);
    let mc = middle_constr.clone();
    middle_constr
        .borrow_mut()
        .set_primary_port(Some(push_z_4_aux_port(&z_middle, mc.clone())));

    let top_l_z_last_port = nth_z_4_aux_Port(&z_top_left, 3).unwrap();
    push_z_4_aux_port(&z_top_left, top_l_z_last_port);
    let _ = insert_z_4_aux_port(&z_top_left, 3, z_top_left.clone());

    let z_middle_middle_ports = nth_z_4_aux_Port(&z_middle, 1)
        .zip(nth_z_4_aux_Port(&z_middle, 2))
        .unwrap();
    let z_top_left_middle_left_port = push_z_4_aux_port(&z_top_left, z_middle_middle_ports.1);
    let z_top_left_middle_right_port = push_z_4_aux_port(&z_top_left, z_middle_middle_ports.0);

    push_z_4_aux_port(&z_middle, z_top_left_middle_right_port);
    push_z_4_aux_port(&z_middle, z_top_left_middle_left_port);
    middle_constr.borrow_mut().set_aux_ports([
        Some(dup_middle_z_bottom.clone()),
        Some(push_z_4_aux_port(&z_middle, mc.clone())),
    ]);

    dup_middle_z_bottom
        .borrow_mut()
        .set_aux_ports([Some(middle_constr.clone()), Some(d_constr.clone())]);

    z_bottom_right
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_make_z_comb() {
        let cases = [
            (0, "Era[@0](v0)"),
            (1, "v0 ~ v1"),
            (2, "Constr[@0](v3, v0, v2)"),
            (3, "Constr[@3](v5, Constr[@0](@3, v0, v2), v4)"),
            (
                4,
                "Constr[@6](v7, Constr[@3](@6, Constr[@0](@3, v0, v2), v4), v6)",
            ),
        ];

        for (case, expected) in cases {
            assert_eq!(
                make_z_comb(case, &mut NameIter::default()).to_string(),
                expected
            );
        }
    }

    #[test]
    fn test_make_d_comb() {
        assert_eq!(
            make_d_comb(&mut NameIter::default()).to_string(),
            "Constr[@6](v7, Constr[@3](@6, Constr[@0](@3, Dup[@9](@3, @0, @0), @9), @9), v6)"
        );
    }

    #[test]
    fn test_make_k_comb() {
        assert_eq!(
            make_k_comb(&mut NameIter::default()).to_string(),
            "Constr[@3](v5, Constr[@0](@3, Constr[@12](@3, Constr[@9](@12, Constr[@6](@9, Dup[@15](@9, @6, @6), @15), @15), @0), Era[@16](@0)), @12)"
        );
    }
}
