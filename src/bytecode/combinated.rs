use crate::{
    heuristics::TypedProgram,
    parser::{
        ast_combinators::{Constructor, Duplicator, Eraser, Expr, Port, Var},
        ast_lafont::Ident,
        naming::NameIter,
    },
};

#[derive(Debug, Clone)]
pub struct CombinatedProgram {
    pub nets: Vec<Port>,
    pub original: TypedProgram,
}

impl CombinatedProgram {
    /// Converts a general program into a program
    /// made with the era, dup, constr combinators
    pub fn compile(program: TypedProgram) -> Self {
        let combinator_nets = program
            .nets
            .iter()
            .filter_map(|n| match (&n.lhs, &n.rhs) {
                (Some(a), None) | (None, Some(a)) => Some(vec![Port::try_from(a.clone()).ok()?]),
                (Some(a), Some(b)) => {
                    let lhs = Port::try_from(a.clone()).ok()?;
                    let rhs = Port::try_from(b.clone()).ok()?;

                    lhs.try_borrow_mut()
                        .ok()?
                        .set_primary_port(Some(rhs.clone()));
                    rhs.try_borrow_mut()
                        .ok()?
                        .set_primary_port(Some(lhs.clone()));

                    Some(vec![lhs, rhs])
                }
                (None, None) => None,
            })
            .flatten()
            .collect::<Vec<_>>();

        Self {
            nets: combinator_nets,
            original: program,
        }
    }
}

/// Inserts a new value in the free var at the specified index in the multiplexor
fn insert_multiplexor_next_port(slf: &Port, to_insert: Port) {
    // Walk the tree until we find a free var to insert in
    let free_idx = slf
        .borrow()
        .aux_ports()
        .iter()
        .enumerate()
        .filter_map(|(i, p)| {
            if p.as_ref().map(|p| p.borrow().is_var()).unwrap_or(true) {
                Some(i)
            } else {
                None
            }
        })
        .last();

    let agent = slf
        .borrow()
        .aux_ports()
        .iter()
        .filter(|p| {
            p.as_ref()
                .map(|p| p.borrow().is_agent())
                .unwrap_or_default()
        })
        .cloned()
        .flatten()
        .last();

    if let Some(idx) = free_idx {
        slf.borrow_mut()
            .insert_aux_port(idx, Some(to_insert.clone()));
        to_insert.borrow_mut().set_primary_port(Some(slf.clone()));
    } else if let Some(port) = agent {
        insert_multiplexor_next_port(&port, to_insert);
    }
}

pub fn make_transpositor(p: usize, q: usize, names: &mut NameIter) -> Port {
    let root = make_autodual_multiplexor(p + q, names);

    // Create 2p dup inputs
    for _ in 0..p {
        let agent: Port = Expr::Constr(Constructor::new()).into();

        let a_var: Port = Expr::Var(Var {
            name: Ident(names.next()),
            port: Some(agent.clone()),
        })
        .into();
        let b_var: Port = Expr::Var(Var {
            name: Ident(names.next()),
            port: Some(agent.clone()),
        })
        .into();

        agent.borrow_mut().set_aux_ports([Some(a_var), Some(b_var)]);

        // For n > 1 last insertion will insert two agents in aux port
        insert_multiplexor_next_port(&root, agent);
    }

    // Q inputs are automatically variables

    root
}

pub fn make_autodual_multiplexor(arity: usize, names: &mut NameIter) -> Port {
    if arity == 0 {
        let e: Port = Expr::Era(Eraser::new()).into();
        let var_a: Port = Expr::Var(Var {
            name: Ident(names.next()),
            port: Some(e.clone()),
        })
        .into();

        e.borrow_mut().set_primary_port(Some(var_a));

        return e;
    }

    if arity == 1 {
        let var_a: Port = Expr::Var(Var {
            name: Ident(names.next()),
            port: None,
        })
        .into();
        let var_b: Port = Expr::Var(Var {
            name: Ident(names.next()),
            port: Some(var_a.clone()),
        })
        .into();

        var_a.borrow_mut().set_primary_port(Some(var_b));

        return var_a;
    }

    let init: Port = {
        let e: Port = Expr::Dup(Duplicator::new()).into();

        let var_a: Port = Expr::Var(Var {
            name: Ident(names.next()),
            port: Some(e.clone()),
        })
        .into();
        let var_b: Port = Expr::Var(Var {
            name: Ident(names.next()),
            port: None,
        })
        .into();
        let var_c: Port = Expr::Var(Var {
            name: Ident(names.next()),
            port: None,
        })
        .into();

        e.borrow_mut().set_primary_port(Some(var_a));
        e.borrow_mut().set_aux_ports([Some(var_b), Some(var_c)]);

        e
    };

    // Continuously add on duplicator until we reach the arity
    let _ = (0..(arity - 2)).fold(
        (init.clone(), 2usize),
        |(acc, prev_var): (Port, usize), _| {
            let var_a: Port = Expr::Var(Var {
                name: Ident((prev_var + 1).to_string()),
                port: None,
            })
            .into();
            let var_b: Port = Expr::Var(Var {
                name: Ident((prev_var + 2).to_string()),
                port: None,
            })
            .into();

            // Append an incremented var and append new node to previous node
            let new_e: Port = Expr::Dup(Duplicator::new()).into();
            new_e.borrow_mut().set_primary_port(Some(acc.clone()));
            new_e.borrow_mut().set_aux_ports([Some(var_a), Some(var_b)]);

            acc.borrow_mut().push_aux_port(Some(new_e.clone()));

            (new_e, prev_var + 2)
        },
    );

    init
}

pub fn make_multiplexor(arity: usize, names: &mut NameIter) -> Port {
    if arity == 0 {
        let e: Port = Expr::Era(Eraser::new()).into();
        let var_a: Port = Expr::Var(Var {
            name: Ident(names.next()),
            port: Some(e.clone()),
        })
        .into();

        e.borrow_mut().set_primary_port(Some(var_a));

        return e;
    }

    if arity == 1 {
        let var_a: Port = Expr::Var(Var {
            name: Ident(names.next()),
            port: None,
        })
        .into();
        let var_b: Port = Expr::Var(Var {
            name: Ident(names.next()),
            port: Some(var_a.clone()),
        })
        .into();

        var_a.borrow_mut().set_primary_port(Some(var_b));

        return var_a;
    }

    let init: Port = {
        let e: Port = Expr::Constr(Constructor::new()).into();

        let var_a: Port = Expr::Var(Var {
            name: Ident(names.next()),
            port: Some(e.clone()),
        })
        .into();
        let var_b: Port = Expr::Var(Var {
            name: Ident(names.next()),
            port: None,
        })
        .into();
        let var_c: Port = Expr::Var(Var {
            name: Ident(names.next()),
            port: None,
        })
        .into();

        e.borrow_mut().set_primary_port(Some(var_a));
        e.borrow_mut().set_aux_ports([Some(var_b), Some(var_c)]);

        e
    };

    // Continuously add on constructor until we reach the arity
    let _ = (0..(arity - 2)).fold(
        (init.clone(), 2usize),
        |(acc, prev_var): (Port, usize), _| {
            let var_a: Port = Expr::Var(Var {
                name: Ident((prev_var + 1).to_string()),
                port: None,
            })
            .into();
            let var_b: Port = Expr::Var(Var {
                name: Ident((prev_var + 2).to_string()),
                port: None,
            })
            .into();

            // Append an incremented var and append new node to previous node
            let new_e: Port = Expr::Constr(Constructor::new()).into();
            new_e.borrow_mut().set_primary_port(Some(acc.clone()));
            new_e.borrow_mut().set_aux_ports([Some(var_a), Some(var_b)]);

            acc.borrow_mut().push_aux_port(Some(new_e.clone()));

            (new_e, prev_var + 2)
        },
    );

    init
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::parser::ast_combinators::port_to_string;
    use test_log::test;

    #[test]
    fn test_make_autodual_multiplexor() {
        let cases = [
            (0, "Era(0)"),
            (1, "0"),
            (2, "Dup(0, 1, 2)"),
            (3, "Dup(0, 1, Dup(3, 4))"),
            (4, "Dup(0, 1, Dup(3, Dup(5, 6)))"),
            (5, "Dup(0, 1, Dup(3, Dup(5, Dup(7, 8))))"),
        ];

        for (case, expected) in cases {
            let found = make_autodual_multiplexor(case, &mut Default::default());

            assert_eq!(port_to_string(&found), expected);
        }
    }

    #[test]
    fn test_make_multiplexor() {
        let cases = [
            (0, "Era(0)"),
            (1, "0"),
            (2, "Constr(0, 1, 2)"),
            (3, "Constr(0, 1, Constr(3, 4))"),
            (4, "Constr(0, 1, Constr(3, Constr(5, 6)))"),
            (5, "Constr(0, 1, Constr(3, Constr(5, Constr(7, 8))))"),
        ];

        for (case, expected) in cases {
            let found = make_multiplexor(case, &mut Default::default());

            assert_eq!(port_to_string(&found), expected);
        }
    }

    #[test]
    fn test_make_transpositor() {
        let cases = [
            (0, 0, "Era(0)"),
            (1, 0, "0"),
            (2, 0, "Dup(0, Constr(5, 6), Constr(3, 4))"),
            (2, 1, "Dup(0, Constr(3, 4), Dup(3, Constr(5, 6)))"),
            (1, 1, "Dup(0, 1, Constr(3, 4))"),
        ];

        for (p, q, expected) in cases {
            let found = make_transpositor(p, q, &mut Default::default());

            assert_eq!(port_to_string(&found), expected);
        }
    }
}
