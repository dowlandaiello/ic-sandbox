use super::{parser::Expr, parser_sk::Expr as SkExpr};
use inetlib::parser::{ast_combinators::Port as AstPort, naming::NameIter};

use builder::{CombinatorBuilder, OwnedNetBuilder};

mod builder;

pub fn compile_sk(e: SkExpr) -> AstPort {
    let mut names = NameIter::default();

    build_compilation_expr(e, &mut names)
        .expand_to_end(&mut names)
        .combinate(&mut Default::default(), &mut names)
}

fn build_compilation_expr(e: SkExpr, names: &mut NameIter) -> OwnedNetBuilder {
    match e {
        SkExpr::Var(v) => OwnedNetBuilder::new(
            CombinatorBuilder::Var {
                name: v,
                primary_port: None,
            },
            names,
        ),
        SkExpr::K(a, b) => {
            let e = OwnedNetBuilder::new(CombinatorBuilder::K { primary_port: None }, names);

            let a_cc = a.map(|a| build_compilation_expr(*a, names));
            let b_cc = b.map(|b| build_compilation_expr(*b, names));

            let constr_child = OwnedNetBuilder::new(
                CombinatorBuilder::Constr {
                    primary_port: Some((0, e.clone())),
                    aux_ports: [None, a_cc.map(|a| (0, a))],
                },
                names,
            );

            let constr_parent = OwnedNetBuilder::new(
                CombinatorBuilder::Constr {
                    primary_port: Some((1, constr_child.clone())),
                    aux_ports: [None, b_cc.map(|b| (0, b))],
                },
                names,
            );

            e.update_with(|builder| {
                builder
                    .clone()
                    .with_primary_port(Some((0, constr_child.clone())))
            });
            constr_child.update_with(|builder| {
                builder
                    .clone()
                    .with_push_aux_port(Some((0, constr_parent.clone())))
            });

            e
        }
        SkExpr::S(a, b, c) => {
            let e = OwnedNetBuilder::new(CombinatorBuilder::S { primary_port: None }, names);

            let a_cc = a.map(|a| build_compilation_expr(*a, names));
            let b_cc = b.map(|b| build_compilation_expr(*b, names));
            let c_cc = c.map(|c| build_compilation_expr(*c, names));

            let constr_child = OwnedNetBuilder::new(
                CombinatorBuilder::Constr {
                    primary_port: Some((0, e.clone())),
                    aux_ports: [None, a_cc.map(|a| (0, a))],
                },
                names,
            );

            let constr_parent = OwnedNetBuilder::new(
                CombinatorBuilder::Constr {
                    primary_port: Some((1, constr_child.clone())),
                    aux_ports: [None, b_cc.map(|b| (0, b))],
                },
                names,
            );

            let constr_parent_parent = OwnedNetBuilder::new(
                CombinatorBuilder::Constr {
                    primary_port: Some((1, constr_parent.clone())),
                    aux_ports: [None, c_cc.map(|c| (0, c))],
                },
                names,
            );

            e.update_with(|builder| {
                builder
                    .clone()
                    .with_primary_port(Some((0, constr_child.clone())))
            });
            constr_child.update_with(|builder| {
                builder
                    .clone()
                    .with_push_aux_port(Some((0, constr_parent.clone())))
            });
            constr_parent.update_with(|builder| {
                builder
                    .clone()
                    .with_push_aux_port(Some((0, constr_parent_parent.clone())))
            });

            e
        }
    }
}

pub fn compile(e: Expr, names: &mut NameIter) -> AstPort {
    todo!()
}

pub fn decompile(p: &AstPort) -> Option<Expr> {
    todo!()
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::parser_sk::{lexer, parser};
    use chumsky::Parser;

    #[test_log::test]
    fn test_compile_simple() {
        let cases = ["(K)", "(S)", "(K(a)(b)))"];

        for case in cases {
            let parsed = parser().parse(lexer().parse(case).unwrap()).unwrap();

            println!("{}", compile_sk(parsed.into()));
        }
    }
}
