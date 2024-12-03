use crate::{
    heuristics::TypedProgram,
    parser::{
        ast_combinators::{Constructor, Eraser, Expr, Port, Var},
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

pub fn make_multiplexor(arity: usize) -> Port {
    if arity == 0 {
        return Expr::Era(Eraser::new()).into();
    }

    if arity == 1 {
        let var_a: Port = Expr::Var(Var {
            name: Ident(String::from("a")),
            port: None,
        })
        .into();
        let var_b: Port = Expr::Var(Var {
            name: Ident(String::from("b")),
            port: Some(var_a.clone()),
        })
        .into();

        var_a.borrow_mut().set_primary_port(Some(var_b));

        return var_a;
    }

    let init: Port = {
        let var_a: Port = Expr::Var(Var {
            name: Ident(String::from("0")),
            port: None,
        })
        .into();
        let var_b: Port = Expr::Var(Var {
            name: Ident(String::from("1")),
            port: None,
        })
        .into();

        let e: Port = Expr::Constr(Constructor::new()).into();

        e.borrow_mut().set_primary_port(Some(var_a));
        e.borrow_mut().set_aux_ports([Some(var_b), None]);

        e
    };

    // Continuously add on constructors until we reach the arity
    let constrs = (0..(arity - 1)).fold((init, 1usize), |(acc, prev_var): (Port, usize), _| {
        let var: Port = Expr::Var(Var {
            name: Ident((prev_var + 1).to_string()),
            port: None,
        })
        .into();

        // Append an incremented var and append new node to previous node
        let new_e: Port = Expr::Constr(Constructor::new()).into();
        new_e.borrow_mut().set_primary_port(Some(acc.clone()));
        new_e.borrow_mut().set_aux_ports([Some(var), None]);

        acc.borrow_mut().push_aux_port(Some(new_e.clone()));

        (new_e, prev_var + 1)
    });

    constrs.0
}
