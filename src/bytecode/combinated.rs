use super::naming::NameIter;
use crate::{
    heuristics::TypedProgram,
    parser::{
        ast_combinators::{Constructor, Duplicator, Eraser, Expr, Port, Var},
        ast_lafont::Ident,
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

        let translated_nets = program
            .nets
            .iter()
            .filter_map(|n| n.lhs.as_ref().zip(n.rhs.as_ref()))
            .map(|(lhs, rhs)| {});

        Self {
            nets: combinator_nets,
            original: program,
        }
    }
}

pub fn make_tranpositor(p: usize, q: usize) -> Port {
    let root = make_autodual_multiplexor(p + q);

    // Create 2p dup inputs
    (0..(2 * p)).step_by(2).fold(root.clone(), |accum, i| {
        let agent: Port = Expr::Constr(Constructor::new()).into();

        let a_var: Port = Expr::Var(Var {
            name: Ident(i.to_string()),
            port: Some(agent.clone()),
        })
        .into();
        let b_var: Port = Expr::Var(Var {
            name: Ident((i + 1).to_string()),
            port: Some(agent.clone()),
        })
        .into();

        agent.borrow_mut().push_aux_port(Some(a_var));
        agent.borrow_mut().push_aux_port(Some(b_var));

        agent.borrow_mut().set_primary_port(Some(accum.clone()));
        accum.borrow_mut().insert_aux_port(0, Some(agent.clone()));

        accum.borrow().aux_ports()[1].clone().unwrap()
    });

    // Q inputs are automatically variables

    root
}

pub fn make_autodual_multiplexor(arity: usize) -> Port {
    if arity == 0 {
        return Expr::Era(Eraser::new()).into();
    }

    if arity == 1 {
        let mut names = NameIter::default();

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
        let mut names = NameIter::default();

        let var_a: Port = Expr::Var(Var {
            name: Ident(names.next()),
            port: None,
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

        let e: Port = Expr::Dup(Duplicator::new()).into();

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

pub fn make_multiplexor(arity: usize) -> Port {
    if arity == 0 {
        return Expr::Era(Eraser::new()).into();
    }

    if arity == 1 {
        let mut names = NameIter::default();

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
        let mut names = NameIter::default();

        let var_a: Port = Expr::Var(Var {
            name: Ident(names.next()),
            port: None,
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

        let e: Port = Expr::Constr(Constructor::new()).into();

        e.borrow_mut().set_primary_port(Some(var_a));
        e.borrow_mut().set_aux_ports([Some(var_b), Some(var_c)]);

        e
    };

    // Continuously add on constructors until we reach the arity
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
            (0, "Era()"),
            (1, "0"),
            (2, "Dup(1, 2)"),
            (3, "Dup(1, Dup(3, 4))"),
            (4, "Dup(1, Dup(3, Dup(5, 6)))"),
            (5, "Dup(1, Dup(3, Dup(5, Dup(7, 8))))"),
        ];

        for (case, expected) in cases {
            let found = make_autodual_multiplexor(case);

            assert_eq!(port_to_string(&found), expected);
        }
    }

    #[test]
    fn test_make_multiplexor() {
        let cases = [
            (0, "Era()"),
            (1, "0"),
            (2, "Constr(1, 2)"),
            (3, "Constr(1, Constr(3, 4))"),
            (4, "Constr(1, Constr(3, Constr(5, 6)))"),
            (5, "Constr(1, Constr(3, Constr(5, Constr(7, 8))))"),
        ];

        for (case, expected) in cases {
            let found = make_multiplexor(case);

            assert_eq!(port_to_string(&found), expected);
        }
    }

    #[test]
    fn test_make_transpositor() {
	let cases = [
	    (0, ")
	];
    }
}
