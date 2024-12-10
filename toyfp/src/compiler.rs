use super::parser::Expr;
use inetlib::parser::{
    ast_combinators::{self as ast_icc, Constructor, Duplicator, Port, Var},
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
}
