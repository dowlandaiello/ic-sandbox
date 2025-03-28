use super::{
    parser::{Expr, Stmt},
    parser_sk::Expr as SkExpr,
};
use ast_ext::Spanned;
use builder::{CombinatorBuilder as SkCombinatorBuilder, OwnedNetBuilder};
use inetlib::{
    parser::{ast_combinators::Port as AstPort, naming::NameIter},
    reducers::combinators::reduce_dyn,
};
use std::collections::{BTreeMap, BTreeSet};
use typing::UntypedExpr;

mod builder;
pub mod graphical;
mod icalc;
pub mod typing;

pub trait CombinatorBuilder: Sized {
    type CPort;
    type EExpr;

    fn decombinate(p: &Self::CPort, names: &NameIter) -> Option<Self::EExpr>;

    fn combinate(&self) -> Self::CPort;

    fn expand_step(&self, names: &NameIter) -> Self;
}

fn next_dedup(
    var: String,
    used_names: &mut BTreeSet<String>,
    available_names: &mut BTreeSet<String>,
) -> String {
    let mut valid_var = var.clone();

    while used_names.contains(&valid_var) {
        valid_var = format!("{}{}", &valid_var, &var);
    }

    used_names.insert(valid_var.clone());
    available_names.insert(valid_var.clone());

    valid_var
}

pub fn compile_sk(e: SkExpr, names: &NameIter) -> AstPort {
    let cc = build_compilation_expr(e.clone(), &names);

    #[cfg(test)]
    cc.checksum();

    cc.clone().iter_tree().for_each(|x| {
        x.expand_step(&names);
    });

    #[cfg(test)]
    cc.checksum();

    let combinated = cc.combinate();

    combinated.checksum();

    tracing::debug!(
        "encoded {} -> {}",
        e,
        combinated.iter_tree_visitor().into_string()
    );

    combinated
}

pub fn decode_sk(p: &AstPort, names: &NameIter) -> SkExpr {
    tracing::debug!("decoding {}", p.iter_tree_visitor().into_string());

    // Incomplete calls are:
    // Kx
    //
    // Sx
    // Sxy
    let alphabet = [SkExpr::S, SkExpr::K];

    let incompletes = alphabet
        .iter()
        .map(|sk_expr| SkExpr::Call {
            callee: Box::new(SkExpr::K),
            params: vec![sk_expr.clone()],
        })
        .chain(alphabet.iter().map(|sk_expr| SkExpr::Call {
            callee: Box::new(SkExpr::S),
            params: vec![sk_expr.clone()],
        }))
        .chain(
            alphabet
                .iter()
                .map(|arg_1| alphabet.iter().map(|arg_2| (arg_1.clone(), arg_2.clone())))
                .flatten()
                .map(|(arg_1, arg_2)| SkExpr::Call {
                    callee: Box::new(SkExpr::S),
                    params: vec![arg_1.clone(), arg_2.clone()],
                }),
        );

    OwnedNetBuilder::decombinate(p, names)
        .or_else(|| {
            incompletes
                .filter_map(|expr| {
                    let cc = compile_sk(expr.clone(), names);
                    let cmp = reduce_dyn(&cc).remove(0);

                    tracing::debug!("attempting incomplete expr: {}", expr);

                    OwnedNetBuilder::decombinate_expr(p.clone(), cmp).then(|| expr)
                })
                .next()
        })
        .expect("invalid SK expression")
}

fn build_compilation_expr(e: SkExpr, names: &NameIter) -> OwnedNetBuilder {
    tracing::trace!("compiling {}", e);

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
                                p.1 .0
                                    .borrow()
                                    .builder
                                    .as_var()
                                    .map(|x| x.starts_with("v"))
                                    .unwrap_or_default()
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
        SkExpr::SPrime => (
            OwnedNetBuilder::new(SkCombinatorBuilder::SPrime { primary_port: None }, names),
            Vec::new(),
        ),
        SkExpr::B => (
            OwnedNetBuilder::new(SkCombinatorBuilder::B { primary_port: None }, names),
            Vec::new(),
        ),
        SkExpr::C => (
            OwnedNetBuilder::new(SkCombinatorBuilder::C { primary_port: None }, names),
            Vec::new(),
        ),
        SkExpr::W => (
            OwnedNetBuilder::new(SkCombinatorBuilder::W { primary_port: None }, names),
            Vec::new(),
        ),
        SkExpr::K => (
            OwnedNetBuilder::new(SkCombinatorBuilder::K { primary_port: None }, names),
            Vec::new(),
        ),
        SkExpr::S => (
            OwnedNetBuilder::new(SkCombinatorBuilder::S { primary_port: None }, names),
            Vec::new(),
        ),
        SkExpr::Call { callee, params } => {
            let a_cc = build_compilation_expr(*callee, names);

            (a_cc, params)
        }
    };

    let last = args.into_iter().fold(builder.clone(), |acc, x| {
        #[cfg(test)]
        builder.checksum();

        let cc = best_port(&best_port(&build_compilation_expr(x, names)).1.encode(names));

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

    tracing::debug!(
        "encoding {} -> {}",
        e.clone(),
        builder.clone().iter_tree().into_string()
    );

    builder
}

fn deduplicate(
    e: Spanned<Expr>,
    used_names: &mut BTreeSet<String>,
    available_names: &mut BTreeSet<String>,
) -> Spanned<Expr> {
    match e {
        Spanned(
            Expr::Abstraction {
                bind_id,
                bind_ty,
                body,
            },
            s,
        ) => {
            let new_var = next_dedup(bind_id.clone().0, used_names, available_names);

            let replaced = replace_occurrences(Spanned(*body.0, body.1), &bind_id, new_var.clone());

            Spanned(
                Expr::Abstraction {
                    bind_id: Spanned(new_var, s.clone()),
                    bind_ty: Spanned(
                        Box::new(
                            deduplicate(
                                Spanned(*bind_ty.0, bind_ty.1.clone()),
                                used_names,
                                available_names,
                            )
                            .0,
                        ),
                        bind_ty.1,
                    ),
                    body: Spanned(
                        Box::new(
                            deduplicate(
                                Spanned(replaced.0, replaced.1.clone()),
                                used_names,
                                available_names,
                            )
                            .0,
                        ),
                        replaced.1,
                    ),
                },
                s,
            )
        }
        Spanned(Expr::Application { lhs, rhs }, s) => Spanned(
            Expr::Application {
                lhs: Spanned(
                    Box::new(
                        deduplicate(Spanned(*lhs.0, lhs.1.clone()), used_names, available_names).0,
                    ),
                    lhs.1,
                ),
                rhs: Spanned(
                    Box::new(
                        deduplicate(Spanned(*rhs.0, rhs.1.clone()), used_names, available_names).0,
                    ),
                    rhs.1,
                ),
            },
            s,
        ),
        v => v,
    }
}

fn remove_root_shadow_vars(e: Spanned<Expr>, names: &NameIter) -> Spanned<Expr> {
    match e {
        Spanned(Expr::Id(v), s) => Spanned(
            {
                if v.starts_with("v") {
                    Expr::Id(Spanned(format!("_{}", v.0), v.1))
                } else {
                    Expr::Id(v)
                }
            },
            s,
        ),
        Spanned(Expr::Application { lhs, rhs }, s) => Spanned(
            Expr::Application {
                lhs: Spanned(
                    Box::new(remove_root_shadow_vars(Spanned(*lhs.0, lhs.1.clone()), names).0),
                    lhs.1,
                ),
                rhs: Spanned(
                    Box::new(remove_root_shadow_vars(Spanned(*rhs.0, rhs.1.clone()), names).0),
                    rhs.1,
                ),
            },
            s,
        ),
        Spanned(
            Expr::Abstraction {
                bind_id,
                bind_ty,
                body,
            },
            s,
        ) => Spanned(
            if bind_id.starts_with("v") {
                let new_bind_id = format!("_{}", bind_id.0);

                Expr::Abstraction {
                    bind_id: Spanned(new_bind_id.clone(), bind_id.1.clone()),
                    bind_ty,
                    body: Spanned(
                        Box::new(
                            remove_root_shadow_vars(
                                replace_occurrences(
                                    Spanned(*body.0, body.1.clone()),
                                    &bind_id,
                                    new_bind_id,
                                ),
                                names,
                            )
                            .0,
                        ),
                        body.1,
                    ),
                }
            } else {
                Expr::Abstraction {
                    bind_id,
                    bind_ty,
                    body: Spanned(
                        Box::new(
                            remove_root_shadow_vars(Spanned(*body.0, body.1.clone()), names).0,
                        ),
                        body.1,
                    ),
                }
            },
            s,
        ),
    }
}

fn replace_occurrences(e: Spanned<Expr>, old: &str, new: String) -> Spanned<Expr> {
    match e {
        Spanned(
            Expr::Abstraction {
                bind_id,
                bind_ty,
                body,
            },
            s,
        ) => {
            if bind_id.0 == old {
                return Spanned(
                    Expr::Abstraction {
                        bind_id,
                        bind_ty: Spanned(
                            Box::new(
                                replace_occurrences(
                                    Spanned(*bind_ty.0, bind_ty.1.clone()),
                                    old,
                                    new.clone(),
                                )
                                .0,
                            ),
                            bind_ty.1,
                        ),
                        body: Spanned(
                            Box::new(
                                replace_occurrences(Spanned(*body.0, body.1.clone()), old, new).0,
                            ),
                            body.1,
                        ),
                    },
                    s,
                );
            }

            Spanned(
                Expr::Abstraction {
                    bind_id,
                    bind_ty: Spanned(
                        Box::new(
                            replace_occurrences(
                                Spanned(*bind_ty.0, bind_ty.1.clone()),
                                old,
                                new.clone(),
                            )
                            .0,
                        ),
                        bind_ty.1,
                    ),
                    body: Spanned(
                        Box::new(replace_occurrences(Spanned(*body.0, body.1.clone()), old, new).0),
                        body.1,
                    ),
                },
                s,
            )
        }
        Spanned(Expr::Application { lhs, rhs }, s) => Spanned(
            Expr::Application {
                lhs: Spanned(
                    Box::new(replace_occurrences(Spanned(*lhs.0, lhs.1), old, new.clone()).0),
                    s.clone(),
                ),
                rhs: Spanned(
                    Box::new(replace_occurrences(Spanned(*rhs.0, rhs.1), old, new.clone()).0),
                    s.clone(),
                ),
            },
            s,
        ),
        Spanned(Expr::Id(v), s) => Spanned(
            Expr::Id(if v.0 == old {
                Spanned(new, s.clone())
            } else {
                Spanned(v.0, s.clone())
            }),
            s,
        ),
    }
}

pub fn compile(stmts: impl Iterator<Item = Spanned<Stmt>> + Clone, names: &NameIter) -> AstPort {
    tracing::trace!(
        "compiling stmts: {}",
        stmts
            .clone()
            .map(|stmt| stmt.to_string())
            .collect::<Vec<_>>()
            .join("\n")
    );

    fn inline(
        e: Spanned<Expr>,
        to_replace: &str,
        def_table: &BTreeMap<String, Spanned<Expr>>,
    ) -> Spanned<Expr> {
        match e {
            Spanned(
                Expr::Abstraction {
                    bind_id,
                    bind_ty,
                    body,
                },
                span,
            ) => Spanned(
                Expr::Abstraction {
                    bind_id,
                    bind_ty: Spanned(
                        Box::new(
                            inline(
                                Spanned(*bind_ty.0, bind_ty.1.clone()),
                                to_replace,
                                def_table,
                            )
                            .0,
                        ),
                        bind_ty.1,
                    ),
                    body: Spanned(
                        Box::new(inline(Spanned(*body.0, body.1.clone()), to_replace, def_table).0),
                        body.1,
                    ),
                },
                span,
            ),
            Spanned(Expr::Application { lhs, rhs }, span) => Spanned(
                Expr::Application {
                    lhs: Spanned(
                        Box::new(inline(Spanned(*lhs.0, lhs.1.clone()), to_replace, def_table).0),
                        lhs.1.clone(),
                    ),
                    rhs: Spanned(
                        Box::new(inline(Spanned(*rhs.0, rhs.1.clone()), to_replace, def_table).0),
                        rhs.1,
                    ),
                },
                span,
            ),
            Spanned(Expr::Id(id), _) => {
                if id.0 == to_replace {
                    def_table
                        .get(&id.0)
                        .cloned()
                        .unwrap_or(Spanned(Expr::Id(id.clone()), id.1))
                } else {
                    Spanned(Expr::Id(id.clone()), id.1)
                }
            }
        }
    }

    let def_table = stmts
        .clone()
        .filter_map(|stmt| match stmt {
            Spanned(Stmt::Def { bind_name, def: d }, s) => {
                Some((bind_name.clone(), Spanned(d.clone(), s)))
            }
            _ => None,
        })
        .collect::<BTreeMap<_, _>>();

    let expr = stmts
        .into_iter()
        .filter_map(|stmt| match stmt {
            Spanned(Stmt::Expr(e), s) => Some(Spanned(e, s)),
            _ => None,
        })
        .next()
        .unwrap();

    let mut inlined = expr;

    while let Some(k) = def_table
        .keys()
        .filter_map(|k| {
            if inlined.contains_var(k) {
                Some(k)
            } else {
                None
            }
        })
        .next()
    {
        inlined = inline(inlined, k, &def_table);
    }

    inlined = deduplicate(
        remove_root_shadow_vars(inlined, &names),
        &mut Default::default(),
        &mut Default::default(),
    );

    tracing::trace!("inlined: {}", inlined.0);

    let cc = graphical::compile(typing::typecheck(inlined), &names);

    #[cfg(test)]
    cc.checksum();

    cc
}

pub fn decompile(p: &AstPort, names: &NameIter) -> Option<UntypedExpr> {
    Some(graphical::decompile(p, names, &mut Default::default()))
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::{
        parser as lc_parser,
        parser_sk::{lexer, parser},
    };
    use ast_ext::Spanned;
    use chumsky::Parser;
    use inetlib::reducers::combinators::{
        buffered::adjacency_matrix::ReducerBuilder, reduce_dyn, Reducer,
    };

    #[test_log::test]
    fn test_eval_var_simple() {
        let (case, expected) = ("((Ka)K)", "a");
        let names = Default::default();

        let lexed = lexer().parse(case).unwrap();
        let parsed = parser().parse(&lexed).unwrap();
        let compiled = compile_sk(parsed.into(), &names);

        let result = reduce_dyn(&compiled);

        assert_eq!(decode_sk(&result[0].orient(), &names).to_string(), expected);
    }

    #[test_log::test]
    fn test_eval_var_discard() {
        let (case, expected) = ("((Ka)b)", "a");
        let names = Default::default();

        let lexed = lexer().parse(case).unwrap();
        let parsed = parser().parse(&lexed).unwrap();
        let compiled = compile_sk(parsed.into(), &names);

        let result = reduce_dyn(&compiled);

        assert_eq!(decode_sk(&result[0].orient(), &names).to_string(), expected);
    }

    #[test_log::test]
    fn test_eval_bool() {
        let (case, expected) = ("(SKKKS)", "(KS)");
        let names = Default::default();

        let lexed = lexer().parse(case).unwrap();
        let parsed = parser().parse(&lexed).unwrap();
        let compiled = compile_sk(parsed.into(), &names);

        let result = reduce_dyn(&compiled);

        assert_eq!(decode_sk(&result[0].orient(), &names).to_string(), expected);
    }

    #[test_log::test]
    fn test_eval_id_lc() {
        let (case, expected) = ("(\\x:_.x a)", "a");
        let names = Default::default();

        let lexed = lc_parser::lexer().parse(case).unwrap();
        let parsed = lc_parser::parser().parse(&lexed).unwrap();
        let compiled = compile(parsed.into_iter(), &names);

        let result = reduce_dyn(&compiled);

        assert_eq!(decode_sk(&result[0].orient(), &names).to_string(), expected);
    }

    #[test_log::test]
    fn test_eval_partial_lc() {
        let (case, expected) = ("(\\x:_.x \\x:_.x)", "\\v3.v3");
        let names = Default::default();

        let lexed = lc_parser::lexer().parse(case).unwrap();
        let parsed = lc_parser::parser().parse(&lexed).unwrap();
        let compiled = compile(parsed.into_iter(), &names);

        let result = reduce_dyn(&compiled);

        assert_eq!(
            decompile(&result[0].orient(), &names).unwrap().to_string(),
            expected
        );
    }

    #[test_log::test]
    fn test_eval_bool_lc() {
        let (case, expected) = ("(\\a:_.\\b:_.a x y)", "x");
        let names = Default::default();

        let lexed = lc_parser::lexer().parse(case).unwrap();
        let parsed = lc_parser::parser().parse(&lexed).unwrap();
        let compiled = compile(parsed.into_iter(), &names);
        let result = reduce_dyn(&compiled);

        assert_eq!(
            decompile(&result[0].orient(), &names).unwrap().to_string(),
            expected
        );
    }

    #[test_log::test]
    fn test_eval_church_lc() {
        let (case, expected) = (
            "id   = \\x:_.x
z    = \\f:_.\\g:_.g
succ = \\n:_.\\f:_.\\x:_.(f (n f x))

(succ z id a)",
            "a",
        );
        let names = Default::default();

        let lexed = lc_parser::lexer().parse(case).unwrap();
        let parsed = lc_parser::parser().parse(&lexed).unwrap();
        let compiled = compile(parsed.into_iter(), &names);
        let result = reduce_dyn(&compiled);

        assert_eq!(
            decompile(&result[0].orient(), &names).unwrap().to_string(),
            expected
        );
    }

    #[test_log::test]
    fn test_eval_id_nested_lc() {
        let (case, expected) = ("(\\x:_.(\\b:_.b x) a)", "a");
        let names = Default::default();

        let lexed = lc_parser::lexer().parse(case).unwrap();
        let parsed = lc_parser::parser().parse(&lexed).unwrap();
        let compiled = compile(parsed.into_iter(), &names);
        let result = reduce_dyn(&compiled);

        assert_eq!(
            decompile(&result[0].orient(), &names).unwrap().to_string(),
            expected
        );
    }

    #[test_log::test]
    fn test_eval_arg_duplication_lc() {
        let (case, expected) = (
            "f = \\x:_.(x x x x x)
(f \\x:_.x)",
            "\\v7.v7",
        );
        let names = Default::default();

        let lexed = lc_parser::lexer().parse(case).unwrap();
        let parsed = lc_parser::parser().parse(&lexed).unwrap();
        let compiled = compile(parsed.into_iter(), &names);
        let result = reduce_dyn(&compiled);

        assert_eq!(
            decompile(&result[0].orient(), &names).unwrap().to_string(),
            expected
        );
    }

    #[test_log::test]
    fn test_eval_arg_duplication_y_lc() {
        let (case, expected) = (
            "Y = \\f:_.(\\x:_.(f \\v:_.(x x v)) \\x:_.(f \\v:_.(x x v)))
f = \\g:_.\\x:_.(x x x x x)
(Y f \\x:_.x)",
            "\\v33.v33",
        );
        let names = Default::default();

        let lexed = lc_parser::lexer().parse(case).unwrap();
        let parsed = lc_parser::parser().parse(&lexed).unwrap();
        let compiled = compile(parsed.into_iter(), &names);
        let result = reduce_dyn(&compiled);

        assert_eq!(
            decompile(&result[0].orient(), &names).unwrap().to_string(),
            expected
        );
    }

    #[test_log::test]
    fn test_eval_bool_true() {
        let (case, expected) = ("(KSK)", "S");
        let names = Default::default();

        let lexed = lexer().parse(case).unwrap();
        let parsed = parser().parse(&lexed).unwrap();
        let compiled = compile_sk(parsed.into(), &names);

        let result = reduce_dyn(&compiled);

        assert_eq!(decode_sk(&result[0].orient(), &names).to_string(), expected);
    }

    #[test_log::test]
    fn test_eval_k_simple() {
        let (case, expected) = ("K", "K");
        let names = Default::default();

        let lexed = lexer().parse(case).unwrap();
        let parsed = parser().parse(&lexed).unwrap();
        let compiled = compile_sk(parsed.into(), &names);

        let result = reduce_dyn(&compiled);

        assert_eq!(decode_sk(&result[0].orient(), &names).to_string(), expected);
    }

    #[test_log::test]
    fn test_eval_k_call() {
        let (case, expected) = ("((KK)K)", "K");
        let names = Default::default();

        let lexed = lexer().parse(case).unwrap();
        let parsed = parser().parse(&lexed).unwrap();
        let compiled = compile_sk(parsed.into(), &names);

        let result = reduce_dyn(&compiled);

        assert_eq!(decode_sk(&result[0].orient(), &names).to_string(), expected);
    }

    #[test_log::test]
    fn test_eval_k_nested() {
        let (case, expected) = ("(K(KK)KK)", "K");
        let names = Default::default();

        let lexed = lexer().parse(case).unwrap();
        let parsed = parser().parse(&lexed).unwrap();
        let compiled = compile_sk(parsed.into(), &names);

        let result = reduce_dyn(&compiled);

        assert_eq!(decode_sk(&result[0].orient(), &names).to_string(), expected);
    }

    #[test_log::test]
    fn test_eval_s() {
        let (case, expected) = ("(SKSK)", "K");
        let names = Default::default();

        let lexed = lexer().parse(case).unwrap();
        let parsed = parser().parse(&lexed).unwrap();
        let compiled = compile_sk(parsed.into(), &names);

        let result = reduce_dyn(&compiled);

        assert_eq!(decode_sk(&result[0].orient(), &names).to_string(), expected);
    }

    #[test_log::test]
    fn test_eval_s_arg_simple() {
        let (case, expected) = ("((KS)K)", "S");
        let names = Default::default();

        let lexed = lexer().parse(case).unwrap();
        let parsed = parser().parse(&lexed).unwrap();
        let compiled = compile_sk(parsed.into(), &names);

        let result = reduce_dyn(&compiled);

        assert_eq!(decode_sk(&result[0].orient(), &names).to_string(), expected);
    }

    #[test_log::test]
    fn test_eval_return_partial() {
        let (case, expected) = ("((K(KS))K)", "(KS)");
        let names = Default::default();

        let lexed = lexer().parse(case).unwrap();
        let parsed = parser().parse(&lexed).unwrap();
        let compiled = compile_sk(parsed.into(), &names);

        let result = reduce_dyn(&compiled);

        assert_eq!(decode_sk(&result[0].orient(), &names).to_string(), expected);
    }

    #[test_log::test]
    fn test_eval_partial() {
        let (case, expected) = ("(KK)", "(KK)");
        let names = Default::default();

        let lexed = lexer().parse(case).unwrap();
        let parsed = parser().parse(&lexed).unwrap();
        let compiled = compile_sk(parsed.into(), &names);

        let result = reduce_dyn(&compiled);

        assert_eq!(decode_sk(&result[0].orient(), &names).to_string(), expected);
    }

    #[test_log::test]
    fn test_eval_partial_s_arg() {
        let (case, expected) = ("(KS)", "(KS)");
        let names = Default::default();

        let lexed = lexer().parse(case).unwrap();
        let parsed = parser().parse(&lexed).unwrap();
        let compiled = compile_sk(parsed.into(), &names);

        let result = reduce_dyn(&compiled);

        assert_eq!(decode_sk(&result[0].orient(), &names).to_string(), expected);
    }

    #[test_log::test]
    fn test_eval_partial_s() {
        let (case, expected) = ("(SK)", "(SK)");
        let names = Default::default();

        let lexed = lexer().parse(case).unwrap();
        let parsed = parser().parse(&lexed).unwrap();
        let compiled = compile_sk(parsed.into(), &names);

        let result = reduce_dyn(&compiled);

        assert_eq!(decode_sk(&result[0].orient(), &names).to_string(), expected);
    }

    #[test_log::test]
    fn test_eval_s_arg() {
        let (case, expected) = ("(((K(KS))K)K)", "S");
        let names = Default::default();

        let lexed = lexer().parse(case).unwrap();
        let parsed = parser().parse(&lexed).unwrap();
        let compiled = compile_sk(parsed.into(), &names);

        let result = reduce_dyn(&compiled);

        assert_eq!(decode_sk(&result[0].orient(), &names).to_string(), expected);
    }

    #[test_log::test]
    fn test_eval_id() {
        let case = "((SK)S)";
        let names = Default::default();

        let lexed = lexer().parse(case).unwrap();
        let parsed = parser().parse(&lexed).unwrap();
        let compiled = compile_sk(parsed.into(), &names);

        let _ = reduce_dyn(&compiled);
    }

    #[test_log::test]
    fn test_eval_id_app_id() {
        let (case, expected) = ("((((SK)S)((SK)S))K)", "K");
        let names = Default::default();

        let lexed = lexer().parse(case).unwrap();
        let parsed = parser().parse(&lexed).unwrap();
        let compiled = compile_sk(parsed.into(), &names);

        let result = reduce_dyn(&compiled);

        assert_eq!(decode_sk(&result[0].orient(), &names).to_string(), expected);
    }

    #[test_log::test]
    fn test_eval_bckw() {
        let cases = [("(CKKK)", "K"), ("(B(KC)KK)", "C"), ("(WKC)", "C")];

        for (case, expected) in cases {
            let names = NameIter::default();

            let lexed = lexer().parse(case).unwrap();
            let parsed = parser().parse(&lexed).unwrap();
            let compiled = compile_sk(parsed.into(), &names);

            let result = reduce_dyn(&compiled);

            assert_eq!(decode_sk(&result[0].orient(), &names).to_string(), expected);
        }
    }

    #[test_log::test]
    fn test_eval_bckw_nested() {
        let cases = [("(WK(CKKK))", "K")];

        for (case, expected) in cases {
            let names = NameIter::default();

            let lexed = lexer().parse(case).unwrap();
            let parsed = parser().parse(&lexed).unwrap();
            let compiled = compile_sk(parsed.into(), &names);

            let result = reduce_dyn(&compiled);

            assert_eq!(decode_sk(&result[0].orient(), &names).to_string(), expected);
        }
    }
}
