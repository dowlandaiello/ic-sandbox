use super::{
    parser::Expr,
    parser_icalc::{
        Abstraction, Application, Definition, Duplication, Expr as IExpr, Stmt as IStmt,
        Superposition, Var as IVar,
    },
    parser_sk::Expr as SkExpr,
};
use builder::{CombinatorBuilder as SkCombinatorBuilder, OwnedNetBuilder};
use inetlib::parser::{
    ast_combinators::{Constructor, Duplicator, Expr as CExpr, Port as AstPort, Var},
    ast_lafont::Ident,
    naming::NameIter,
};
use std::collections::{BTreeMap, BTreeSet};

mod builder;
mod icalc;

pub trait CombinatorBuilder: Sized {
    type CPort;
    type EExpr;

    fn decombinate(p: &Self::CPort) -> Option<Self::EExpr>;

    fn combinate(&self, names: &NameIter) -> Self::CPort;

    fn expand_step(&self, names: &NameIter) -> Self;
}

pub fn decompile_icalc(p: AstPort, tags: &BTreeMap<usize, String>) -> IExpr {
    todo!()
}

fn inline_icalc(e: IExpr, def_table: &BTreeMap<String, IExpr>) -> IExpr {
    match e {
        IExpr::Abstraction(Abstraction { bind_var, body }) => IExpr::Abstraction(Abstraction {
            bind_var,
            body: Box::new(inline_icalc(*body, def_table)),
        }),
        IExpr::Application(Application(lhs, rhs)) => IExpr::Application(Application(
            Box::new(inline_icalc(*lhs, def_table)),
            Box::new(inline_icalc(*rhs, def_table)),
        )),
        IExpr::Duplication(Duplication {
            tag,
            pair,
            to_clone,
            in_expr,
        }) => IExpr::Duplication(Duplication {
            tag,
            pair,
            to_clone: Box::new(inline_icalc(*to_clone, def_table)),
            in_expr: Box::new(inline_icalc(*in_expr, def_table)),
        }),
        IExpr::Superposition(Superposition { tag, lhs, rhs }) => {
            IExpr::Superposition(Superposition {
                tag,
                lhs: Box::new(inline_icalc(*lhs, def_table)),
                rhs: Box::new(inline_icalc(*rhs, def_table)),
            })
        }
        IExpr::Variable(v) => def_table.get(&v.0).cloned().unwrap_or(IExpr::Variable(v)),
    }
}

fn next_dedup(
    var: String,
    used_names: &mut BTreeSet<String>,
    available_names: &mut BTreeSet<String>,
) -> String {
    let mut valid_var = var.clone();

    while used_names.contains(&valid_var) && !available_names.remove(&valid_var) {
        valid_var = format!("{}{}", &valid_var, &var);
    }

    used_names.insert(valid_var.clone());
    available_names.insert(valid_var.clone());

    valid_var
}

fn replace_occurrences(e: &mut IExpr, old: &str, new: String) {
    match e {
        IExpr::Abstraction(Abstraction { bind_var, body }) => {
            if bind_var == old {
                *bind_var = new.clone();
            }

            replace_occurrences(body, old, new);
        }
        IExpr::Application(Application(lhs, rhs)) => {
            replace_occurrences(lhs, old, new.clone());
            replace_occurrences(rhs, old, new.clone());
        }
        IExpr::Duplication(Duplication {
            pair,
            to_clone,
            in_expr,
            ..
        }) => {
            if pair.0 == old {
                (*pair).0 = new.clone();
            }

            if pair.1 == old {
                (*pair).0 = new.clone();
            }

            replace_occurrences(to_clone, old, new.clone());
            replace_occurrences(in_expr, old, new.clone());
        }
        IExpr::Superposition(Superposition { lhs, rhs, .. }) => {
            replace_occurrences(lhs, old, new.clone());
            replace_occurrences(rhs, old, new.clone());
        }
        IExpr::Variable(v) => {
            if v.0 == old {
                (*v).0 = new;
            }
        }
    }
}

fn deduplicate(
    e: &mut IExpr,
    used_names: &mut BTreeSet<String>,
    available_names: &mut BTreeSet<String>,
) {
    match e {
        IExpr::Abstraction(Abstraction { bind_var, body }) => {
            let new_var = next_dedup(bind_var.clone(), used_names, available_names);

            *bind_var = new_var.clone();

            replace_occurrences(body.as_mut(), bind_var, new_var.clone());

            deduplicate(body, used_names, available_names);
        }
        IExpr::Application(Application(lhs, rhs)) => {
            deduplicate(lhs, used_names, available_names);
            deduplicate(rhs, used_names, available_names);
        }
        IExpr::Duplication(Duplication {
            pair,
            to_clone,
            in_expr,
            ..
        }) => {
            let new_a = next_dedup(pair.0.clone(), used_names, available_names);
            let new_b = next_dedup(pair.1.clone(), used_names, available_names);

            replace_occurrences(in_expr.as_mut(), pair.0.as_str(), new_a);
            replace_occurrences(in_expr.as_mut(), pair.1.as_str(), new_b);

            deduplicate(to_clone, used_names, available_names);
            deduplicate(in_expr, used_names, available_names);
        }
        IExpr::Superposition(Superposition { tag: _, lhs, rhs }) => {
            deduplicate(lhs, used_names, available_names);
            deduplicate(rhs, used_names, available_names);
        }
        IExpr::Variable(v) => {
            let new_var = next_dedup(v.0.clone(), used_names, available_names);
            (*v).0 = new_var;
        }
    }
}

fn make_def_table_icalc(s: &Vec<IStmt>) -> BTreeMap<String, IExpr> {
    s.iter()
        .filter_map(|stmt| match stmt {
            IStmt::Def(d) => Some((d.name.clone(), d.definition.clone())),
            _ => None,
        })
        .collect::<BTreeMap<_, _>>()
}

fn cc_expr(
    e: IExpr,
    net: &mut Vec<AstPort>,
    tags: &mut BTreeMap<usize, String>,
    names: &mut NameIter,
) -> AstPort {
    tracing::trace!("compiling {:?}", e);

    match e {
        IExpr::Abstraction(Abstraction { bind_var, body }) => {
            let body_cc = cc_expr(*body, net, tags, names);
            let var_cc = CExpr::Var(Var {
                name: Ident(bind_var.to_string()),
                port: None,
            })
            .into_port(names);

            let lam = CExpr::Constr(Constructor {
                primary_port: None,
                aux_ports: [Some((0, body_cc.clone())), Some((0, var_cc.clone()))],
            })
            .into_port(names);

            var_cc.borrow_mut().set_primary_port(Some((2, lam.clone())));
            body_cc
                .borrow_mut()
                .set_primary_port(Some((1, lam.clone())));

            lam
        }
        IExpr::Application(Application(lhs, rhs)) => {
            let lhs_cc = cc_expr(*lhs, net, tags, names);
            let rhs_cc = cc_expr(*rhs, net, tags, names);

            let ret_var = CExpr::Var(Var {
                name: Ident("ret".into()),
                port: None,
            })
            .into_port(names);

            let app = CExpr::Constr(Constructor {
                primary_port: Some((0, lhs_cc.clone())),
                aux_ports: [Some((0, ret_var.clone())), Some((0, rhs_cc.clone()))],
            })
            .into_port(names);

            ret_var
                .borrow_mut()
                .set_primary_port(Some((1, app.clone())));
            rhs_cc.borrow_mut().set_primary_port(Some((2, app.clone())));

            lhs_cc.borrow_mut().set_primary_port(Some((0, app.clone())));

            net.push(lhs_cc.clone());

            lhs_cc
        }
        IExpr::Duplication(Duplication {
            pair: (a, b),
            to_clone,
            in_expr,
            tag,
        }) => {
            let a_cc = CExpr::Var(Var {
                name: Ident(a),
                port: None,
            })
            .into_port(names);
            let b_cc = CExpr::Var(Var {
                name: Ident(b),
                port: None,
            })
            .into_port(names);
            let let_cc = CExpr::Dup(Duplicator {
                primary_port: None,
                aux_ports: [Some((0, b_cc.clone())), Some((0, a_cc.clone()))],
            })
            .into_port(names);

            cc_expr(*in_expr, net, tags, names);

            tags.insert(let_cc.id, tag);

            a_cc.borrow_mut()
                .set_primary_port(Some((2, let_cc.clone())));
            a_cc.borrow_mut()
                .set_primary_port(Some((2, let_cc.clone())));

            let pair_cc = cc_expr(*to_clone, net, tags, names);

            pair_cc
                .borrow_mut()
                .set_primary_port(Some((0, let_cc.clone())));
            let_cc
                .borrow_mut()
                .set_primary_port(Some((0, pair_cc.clone())));

            net.push(pair_cc);

            let_cc
        }
        IExpr::Superposition(Superposition { tag, lhs, rhs }) => {
            let lhs_cc = cc_expr(*lhs, net, tags, names);
            let rhs_cc = cc_expr(*rhs, net, tags, names);

            let pair_cc = CExpr::Dup(Duplicator {
                primary_port: None,
                aux_ports: [Some((0, lhs_cc.clone())), Some((0, rhs_cc.clone()))],
            })
            .into_port(names);

            lhs_cc
                .borrow_mut()
                .set_primary_port(Some((1, pair_cc.clone())));
            rhs_cc
                .borrow_mut()
                .set_primary_port(Some((2, pair_cc.clone())));

            tags.insert(pair_cc.id, tag);

            pair_cc
        }
        IExpr::Variable(IVar(i)) => CExpr::Var(Var {
            name: Ident(i),
            port: None,
        })
        .into_port(names),
    }
}

pub fn compile_icalc(mut s: Vec<IStmt>) -> (Vec<AstPort>, BTreeMap<usize, String>) {
    let mut names = Default::default();
    let mut net = Default::default();
    let mut tags = Default::default();
    let mut used_names = Default::default();

    s.iter_mut()
        .map(|stmt| match stmt {
            IStmt::Def(Definition {
                name: _,
                definition,
            }) => definition,
            IStmt::Expr(e) => e,
        })
        .for_each(|e| {
            deduplicate(e, &mut used_names, &mut Default::default());
        });

    let def_table = make_def_table_icalc(&s);

    let expr = if let Some(root) = s
        .iter()
        .filter_map(|stmt| match stmt {
            IStmt::Expr(e) => Some(e),
            _ => None,
        })
        .next()
    {
        root
    } else {
        return Default::default();
    };

    let inlined = inline_icalc(expr.clone(), &def_table);

    println!("{}", inlined);

    let bruh = cc_expr(inlined, &mut net, &mut tags, &mut names);

    println!("{}", bruh.clone().iter_tree_visitor().into_string());

    (net, tags)
}

pub fn compile_sk(e: SkExpr) -> AstPort {
    let mut names = NameIter::default();

    let cc = build_compilation_expr(e, &mut names);

    #[cfg(test)]
    cc.checksum();

    cc.clone().iter_tree().for_each(|x| {
        x.expand_step(&mut names);
    });

    #[cfg(test)]
    cc.checksum();

    let combinated = cc.combinate(&mut names);

    #[cfg(test)]
    combinated.checksum();

    combinated
}

pub fn decode_sk(p: &AstPort) -> SkExpr {
    tracing::trace!("decoding {}", p);

    OwnedNetBuilder::decombinate(p).expect("invalid SK expression")
}

fn build_compilation_expr(e: SkExpr, names: &NameIter) -> OwnedNetBuilder {
    tracing::trace!("compiling {:?}", e);

    let best_port = |p: &OwnedNetBuilder| -> (usize, OwnedNetBuilder) {
        p.clone()
            .iter_tree()
            .map(|x| {
                x.0.borrow()
                    .builder
                    .iter_ports()
                    .enumerate()
                    .filter(|(_, p)| {
                        p.is_none()
                            || p.map(|p| {
                                matches!(p.1 .0.borrow().builder, SkCombinatorBuilder::Var { .. })
                            })
                            .unwrap_or_default()
                    })
                    .map(|(i, _)| (i, x.clone()))
                    .next()
            })
            .flatten()
            .next()
            .unwrap_or((1, p.clone()))
    };

    let (builder, args) = match e.clone() {
        SkExpr::Var(v) => {
            return OwnedNetBuilder::new(
                SkCombinatorBuilder::Var {
                    name: v,
                    primary_port: None,
                },
                names,
            );
        }
        SkExpr::K => (
            OwnedNetBuilder::new(SkCombinatorBuilder::K { primary_port: None }, names),
            Vec::new(),
        ),
        SkExpr::S => (
            OwnedNetBuilder::new(SkCombinatorBuilder::S { primary_port: None }, names),
            Vec::new(),
        ),
        SkExpr::Call(a, b) => {
            let a_cc = build_compilation_expr(*a, names);

            (a_cc, vec![*b])
        }
    };

    let last = args.into_iter().fold(builder.clone(), |acc, x| {
        #[cfg(test)]
        builder.checksum();

        let cc = best_port(&build_compilation_expr(x, names).encode(names));

        let arg_handle = OwnedNetBuilder::new(
            SkCombinatorBuilder::Constr {
                primary_port: None,
                aux_ports: [const { None }; 2],
            },
            names,
        );

        OwnedNetBuilder::connect((2, arg_handle.clone()), cc);

        let ins_parent_port = best_port(&acc);

        OwnedNetBuilder::connect((0, arg_handle.clone()), ins_parent_port);

        arg_handle
    });

    last.make_root(names);

    builder
        .clone()
        .iter_tree()
        .for_each(|x| tracing::trace!("encoding {} -> {:?}", e.clone(), x));

    builder
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
    use crate::{
        parser_icalc,
        parser_sk::{lexer, parser},
    };
    use ast_ext::Spanned;
    use chumsky::Parser;
    use inetlib::reducers::combinators::reduce_dyn;

    #[test_log::test]
    fn test_eval_k_simple() {
        let (case, expected) = ("K", "K");

        let parsed = parser().parse(lexer().parse(case).unwrap()).unwrap();
        let compiled = compile_sk(parsed.into());

        let result = reduce_dyn(&compiled);

        assert_eq!(decode_sk(&result[0].orient()).to_string(), expected);
    }

    #[test_log::test]
    fn test_eval_k_call() {
        let (case, expected) = ("((KK)K)", "K");

        let parsed = parser().parse(lexer().parse(case).unwrap()).unwrap();
        let compiled = compile_sk(parsed.into());

        let result = reduce_dyn(&compiled);

        assert_eq!(decode_sk(&result[0].orient()).to_string(), expected);
    }

    #[test_log::test]
    fn test_eval_k_nested() {
        let (case, expected) = ("((K((KK)K))K)", "K");

        let parsed = parser().parse(lexer().parse(case).unwrap()).unwrap();
        let compiled = compile_sk(parsed.into());

        let result = reduce_dyn(&compiled);

        assert_eq!(decode_sk(&result[0].orient()).to_string(), expected);
    }

    #[test_log::test]
    fn test_eval_s() {
        let (case, expected) = ("(((SK)S)K)", "K");

        let parsed = parser().parse(lexer().parse(case).unwrap()).unwrap();
        let compiled = compile_sk(parsed.into());

        let result = reduce_dyn(&compiled);

        assert_eq!(decode_sk(&result[0].orient()).to_string(), expected);
    }

    #[test_log::test]
    fn test_eval_s_arg() {
        let (case, expected) = ("(((K(KS))K)K)", "(KK)");

        let parsed = parser().parse(lexer().parse(case).unwrap()).unwrap();
        let compiled = compile_sk(parsed.into());

        let result = reduce_dyn(&compiled);

        assert_eq!(decode_sk(&result[0].orient()).to_string(), expected);
    }

    #[test_log::test]
    fn test_eval_partial() {
        let (case, expected) = ("S", "(KK)");

        let parsed = parser().parse(lexer().parse(case).unwrap()).unwrap();
        let compiled = compile_sk(parsed.into());

        let result = reduce_dyn(&compiled);

        assert_eq!(decode_sk(&result[0].orient()).to_string(), expected);
    }

    #[test_log::test]
    fn test_cc_icalc() {
        let case = "def Z = \\s \\z z
def S = \\n \\s \\z (s n)
(S Z)";

        let parsed = parser_icalc::parser()
            .parse(
                parser_icalc::lexer()
                    .parse(case)
                    .unwrap()
                    .into_iter()
                    .flatten()
                    .collect::<Vec<_>>(),
            )
            .unwrap()
            .into_iter()
            .map(|Spanned(x, _)| x)
            .collect();

        let compiled = compile_icalc(parsed);
    }
}
