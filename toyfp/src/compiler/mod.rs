use super::{
    parser::{Expr, Stmt},
    parser_icalc::{
        Abstraction, Application, Definition, Duplication, Expr as IExpr, Stmt as IStmt,
        Superposition, Var as IVar,
    },
    parser_sk::Expr as SkExpr,
};
use builder::{CombinatorBuilder as SkCombinatorBuilder, OwnedNetBuilder};
use inetlib::{
    parser::{
        ast_combinators::{Constructor, Duplicator, Expr as CExpr, Port as AstPort, Var},
        ast_lafont::Ident,
        naming::NameIter,
    },
    reducers::combinators::reduce_dyn,
};
use std::{
    collections::{BTreeMap, BTreeSet},
    fmt,
};

mod builder;
mod icalc;

pub trait CombinatorBuilder: Sized {
    type CPort;
    type EExpr;

    fn decombinate(p: &Self::CPort, names: &NameIter) -> Option<Self::EExpr>;

    fn combinate(&self) -> Self::CPort;

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

    let bruh = cc_expr(inlined, &mut net, &mut tags, &mut names);

    (net, tags)
}

pub fn compile_sk(e: SkExpr, names: &NameIter) -> AstPort {
    let cc = build_compilation_expr(e.clone(), false, &names);

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

fn build_compilation_expr(e: SkExpr, is_arg: bool, names: &NameIter) -> OwnedNetBuilder {
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
        SkExpr::K => (
            OwnedNetBuilder::new(SkCombinatorBuilder::K { primary_port: None }, names),
            Vec::new(),
        ),
        SkExpr::S => (
            OwnedNetBuilder::new(SkCombinatorBuilder::S { primary_port: None }, names),
            Vec::new(),
        ),
        SkExpr::Call { callee, params } => {
            let a_cc = build_compilation_expr(*callee, false, names);

            (a_cc, params)
        }
    };

    let last = args.into_iter().fold(builder.clone(), |acc, x| {
        #[cfg(test)]
        builder.checksum();

        let cc = best_port(
            &best_port(&build_compilation_expr(x, true, names))
                .1
                .encode(names),
        );

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

fn mk_id() -> SkExpr {
    SkExpr::Call {
        callee: Box::new(SkExpr::S),
        params: vec![SkExpr::K, SkExpr::S],
    }
}

pub fn compile(stmts: impl Iterator<Item = Stmt> + Clone, names: &NameIter) -> AstPort {
    #[derive(Clone, Debug)]
    enum MixedExpr {
        S,
        K,
        Id(String),
        Abstraction {
            bind_id: String,
            body: Box<MixedExpr>,
        },
        Application {
            callee: Box<MixedExpr>,
            params: Vec<MixedExpr>,
        },
    }

    impl fmt::Display for MixedExpr {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            match self {
                Self::S => write!(f, "S"),
                Self::K => write!(f, "K"),
                Self::Id(id) => write!(f, "{}", id),
                Self::Abstraction { bind_id, body } => write!(f, "\\{}.{}", bind_id, body),
                Self::Application { callee, params } => write!(
                    f,
                    "({} {})",
                    callee,
                    params
                        .iter()
                        .map(|param| param.to_string())
                        .collect::<Vec<_>>()
                        .join(" ")
                ),
            }
        }
    }

    impl From<Expr> for MixedExpr {
        fn from(e: Expr) -> Self {
            match e {
                Expr::Abstraction { bind_id, body } => Self::Abstraction {
                    bind_id,
                    body: Box::new((*body).into()),
                },
                Expr::Application { lhs, rhs } => Self::Application {
                    callee: Box::new((*lhs).into()),
                    params: vec![(*rhs).into()],
                },
                Expr::Id(id) => Self::Id(id),
            }
        }
    }

    impl From<MixedExpr> for SkExpr {
        fn from(e: MixedExpr) -> Self {
            match e {
                MixedExpr::Abstraction { .. } => unreachable!(),
                MixedExpr::Application { callee, params } => Self::Call {
                    callee: Box::new((*callee).into()),
                    params: params.into_iter().map(|param| param.into()).collect(),
                },
                MixedExpr::Id(id) => Self::Var(id),
                MixedExpr::K => Self::K,
                MixedExpr::S => Self::S,
            }
        }
    }

    impl MixedExpr {
        fn is_all_sk(&self) -> bool {
            match self {
                Self::Abstraction { .. } => false,
                Self::Application { callee, params } => {
                    callee.is_all_sk() && params.iter().all(|param| param.is_all_sk())
                }
                Self::Id(_) | Self::S | Self::K => true,
            }
        }

        fn flatten(self) -> Self {
            match self {
                Self::Application { callee, mut params } => {
                    let inner_param = params.remove(0);

                    Self::Application {
                        callee: Box::new(Self::Application {
                            callee,
                            params: vec![inner_param],
                        }),
                        params,
                    }
                }
                x => x,
            }
        }

        fn eliminate(&mut self) {
            if let Self::Abstraction { bind_id, body } = self {
                match body.as_mut() {
                    Self::Application { callee, params } => {
                        let lhs = callee;
                        let rhs = params.remove(0);

                        *self = Self::Application {
                            callee: Box::new(Self::S),
                            params: vec![
                                Self::Abstraction {
                                    bind_id: bind_id.clone(),
                                    body: lhs.clone(),
                                },
                                Self::Abstraction {
                                    bind_id: bind_id.clone(),
                                    body: Box::new(rhs),
                                },
                            ],
                        }
                    }
                    Self::Id(id) if id == bind_id => {
                        *self = Self::Application {
                            callee: Box::new(Self::S),
                            params: vec![Self::K, Self::S],
                        }
                    }
                    id @ Self::Id(_) => {
                        *self = Self::Application {
                            callee: Box::new(Self::K),
                            params: vec![id.clone()],
                        };
                    }
                    cnst => {
                        *self = Self::Application {
                            callee: Box::new(Self::K),
                            params: vec![cnst.clone()],
                        };
                    }
                }
            }
        }

        fn eliminate_innermost_abstraction(&mut self) -> bool {
            if self.is_all_sk() {
                return false;
            }

            match self {
                Self::S => false,
                Self::K => false,
                Self::Id(_) => false,
                Self::Abstraction { body, .. } => {
                    if !body.eliminate_innermost_abstraction() {
                        self.eliminate();
                    }

                    true
                }
                Self::Application { callee, params } => {
                    callee.eliminate_innermost_abstraction()
                        || params
                            .iter_mut()
                            .any(|x| x.eliminate_innermost_abstraction())
                }
            }
        }
    }

    fn inline(e: Expr, def_table: &BTreeMap<String, Expr>) -> Expr {
        match e {
            Expr::Abstraction { bind_id, body } => Expr::Abstraction {
                bind_id,
                body: Box::new(inline(*body, def_table)),
            },
            Expr::Application { lhs, rhs } => Expr::Application {
                lhs: Box::new(inline(*lhs, def_table)),
                rhs: Box::new(inline(*rhs, def_table)),
            },
            Expr::Id(id) => def_table.get(&id).cloned().unwrap_or(Expr::Id(id)),
        }
    }

    fn precompile(e: Expr) -> SkExpr {
        let mut buffer: MixedExpr = e.into();

        tracing::debug!("eliminating abstraction in {}", buffer);

        while buffer.eliminate_innermost_abstraction() {
            tracing::debug!("eliminating abstraction in {}", buffer);
        }

        buffer.into()
    }

    let def_table = stmts
        .clone()
        .filter_map(|stmt| match stmt {
            Stmt::Def { bind_name, def: d } => Some((bind_name.clone(), d.clone())),
            _ => None,
        })
        .collect::<BTreeMap<_, _>>();

    let expr = stmts
        .into_iter()
        .filter_map(|stmt| match stmt {
            Stmt::Expr(e) => Some(e),
            _ => None,
        })
        .next()
        .unwrap();

    let inlined = inline(expr, &def_table);
    let sk = precompile(inlined);

    let cc = compile_sk(sk, names);

    cc
}

pub fn decompile(p: &AstPort) -> Option<Expr> {
    let names = Default::default();

    let dec_sk = decode_sk(p, &names);

    if let SkExpr::Var(v) = dec_sk {
        return Some(Expr::Id(v));
    }

    if dec_sk == mk_id() {
        let bind_name = names.next_var_name();

        return Some(Expr::Abstraction {
            bind_id: bind_name.clone(),
            body: Box::new(Expr::Id(bind_name.clone())),
        });
    }

    unimplemented!()
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::{
        parser as lc_parser, parser_icalc,
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

        let parsed = parser().parse(lexer().parse(case).unwrap()).unwrap();
        let compiled = compile_sk(parsed.into(), &names);

        let result = reduce_dyn(&compiled);

        assert_eq!(decode_sk(&result[0].orient(), &names).to_string(), expected);
    }

    #[test_log::test]
    fn test_eval_var_discard() {
        let (case, expected) = ("((Ka)b)", "a");
        let names = Default::default();

        let parsed = parser().parse(lexer().parse(case).unwrap()).unwrap();
        let compiled = compile_sk(parsed.into(), &names);

        let result = reduce_dyn(&compiled);

        assert_eq!(decode_sk(&result[0].orient(), &names).to_string(), expected);
    }

    #[test_log::test]
    fn test_eval_bool() {
        let (case, expected) = ("(SKKKS)", "(KS)");
        let names = Default::default();

        let parsed = parser().parse(lexer().parse(case).unwrap()).unwrap();
        let compiled = compile_sk(parsed.into(), &names);

        let result = reduce_dyn(&compiled);

        assert_eq!(decode_sk(&result[0].orient(), &names).to_string(), expected);
    }

    #[test_log::test]
    fn test_eval_id_lc() {
        let (case, expected) = ("(\\x.x a)", "a");
        let names = Default::default();

        let parsed = lc_parser::parser()
            .parse(lc_parser::lexer().parse(case).unwrap())
            .unwrap();
        let compiled = compile(parsed.into_iter().map(|Spanned(x, _)| x), &names);

        let result = reduce_dyn(&compiled);

        assert_eq!(decode_sk(&result[0].orient(), &names).to_string(), expected);
    }

    #[test_log::test]
    fn test_eval_bool_lc() {
        let (case, expected) = ("(\\a.\\b.a x y)", "x");
        let names = Default::default();

        let parsed = lc_parser::parser()
            .parse(lc_parser::lexer().parse(case).unwrap())
            .unwrap();
        let compiled = compile(parsed.into_iter().map(|Spanned(x, _)| x), &names);
        let result = reduce_dyn(&compiled);

        assert_eq!(
            decompile(&result[0].orient()).unwrap().to_string(),
            expected
        );
    }

    #[test_log::test]
    fn test_eval_church_lc() {
        let (case, expected) = (
            "id   = \\x.x
z    = \\f.\\g.g
succ = \\n.\\f.\\x.(f (n f x))

(succ z id a)",
            "a",
        );
        let names = Default::default();

        let parsed = lc_parser::parser()
            .parse(lc_parser::lexer().parse(case).unwrap())
            .unwrap();
        let compiled = compile(parsed.into_iter().map(|Spanned(x, _)| x), &names);
        let result = reduce_dyn(&compiled);

        assert_eq!(
            decompile(&result[0].orient()).unwrap().to_string(),
            expected
        );
    }

    #[test_log::test]
    fn test_eval_id_nested_lc() {
        let (case, expected) = ("(\\x.(\\b.b x) a)", "a");
        let names = Default::default();

        let parsed = lc_parser::parser()
            .parse(lc_parser::lexer().parse(case).unwrap())
            .unwrap();
        let compiled = compile(parsed.into_iter().map(|Spanned(x, _)| x), &names);
        let result = reduce_dyn(&compiled);

        assert_eq!(
            decompile(&result[0].orient()).unwrap().to_string(),
            expected
        );
    }

    #[test_log::test]
    fn test_eval_bool_true() {
        let (case, expected) = ("(KSK)", "S");
        let names = Default::default();

        let parsed = parser().parse(lexer().parse(case).unwrap()).unwrap();
        let compiled = compile_sk(parsed.into(), &names);

        let result = reduce_dyn(&compiled);

        assert_eq!(decode_sk(&result[0].orient(), &names).to_string(), expected);
    }

    #[test_log::test]
    fn test_eval_k_simple() {
        let (case, expected) = ("K", "K");
        let names = Default::default();

        let parsed = parser().parse(lexer().parse(case).unwrap()).unwrap();
        let compiled = compile_sk(parsed.into(), &names);

        let result = reduce_dyn(&compiled);

        assert_eq!(decode_sk(&result[0].orient(), &names).to_string(), expected);
    }

    #[test_log::test]
    fn test_eval_k_call() {
        let (case, expected) = ("((KK)K)", "K");
        let names = Default::default();

        let parsed = parser().parse(lexer().parse(case).unwrap()).unwrap();
        let compiled = compile_sk(parsed.into(), &names);

        let result = reduce_dyn(&compiled);

        assert_eq!(decode_sk(&result[0].orient(), &names).to_string(), expected);
    }

    #[test_log::test]
    fn test_eval_k_nested() {
        let (case, expected) = ("(K(KK)KK)", "K");
        let names = Default::default();

        let parsed = parser().parse(lexer().parse(case).unwrap()).unwrap();
        let compiled = compile_sk(parsed.into(), &names);

        let result = reduce_dyn(&compiled);

        assert_eq!(decode_sk(&result[0].orient(), &names).to_string(), expected);
    }

    #[test_log::test]
    fn test_eval_s() {
        let (case, expected) = ("(SKSK)", "K");
        let names = Default::default();

        let parsed = parser().parse(lexer().parse(case).unwrap()).unwrap();
        let compiled = compile_sk(parsed.into(), &names);

        let result = reduce_dyn(&compiled);

        assert_eq!(decode_sk(&result[0].orient(), &names).to_string(), expected);
    }

    #[test_log::test]
    fn test_eval_s_arg_simple() {
        let (case, expected) = ("((KS)K)", "S");
        let names = Default::default();

        let parsed = parser().parse(lexer().parse(case).unwrap()).unwrap();
        let compiled = compile_sk(parsed.into(), &names);

        let result = reduce_dyn(&compiled);

        assert_eq!(decode_sk(&result[0].orient(), &names).to_string(), expected);
    }

    #[test_log::test]
    fn test_eval_return_partial() {
        let (case, expected) = ("((K(KS))K)", "(KS)");
        let names = Default::default();

        let parsed = parser().parse(lexer().parse(case).unwrap()).unwrap();
        let compiled = compile_sk(parsed.into(), &names);

        let result = reduce_dyn(&compiled);

        assert_eq!(decode_sk(&result[0].orient(), &names).to_string(), expected);
    }

    #[test_log::test]
    fn test_eval_partial() {
        let (case, expected) = ("(KK)", "(KK)");
        let names = Default::default();

        let parsed = parser().parse(lexer().parse(case).unwrap()).unwrap();
        let compiled = compile_sk(parsed.into(), &names);

        let result = reduce_dyn(&compiled);

        assert_eq!(decode_sk(&result[0].orient(), &names).to_string(), expected);
    }

    #[test_log::test]
    fn test_eval_partial_s_arg() {
        let (case, expected) = ("(KS)", "(KS)");
        let names = Default::default();

        let parsed = parser().parse(lexer().parse(case).unwrap()).unwrap();
        let compiled = compile_sk(parsed.into(), &names);

        let result = reduce_dyn(&compiled);

        assert_eq!(decode_sk(&result[0].orient(), &names).to_string(), expected);
    }

    #[test_log::test]
    fn test_eval_partial_s() {
        let (case, expected) = ("(SK)", "(SK)");
        let names = Default::default();

        let parsed = parser().parse(lexer().parse(case).unwrap()).unwrap();
        let compiled = compile_sk(parsed.into(), &names);

        let result = reduce_dyn(&compiled);

        assert_eq!(decode_sk(&result[0].orient(), &names).to_string(), expected);
    }

    #[test_log::test]
    fn test_eval_s_arg() {
        let (case, expected) = ("(((K(KS))K)K)", "S");
        let names = Default::default();

        let parsed = parser().parse(lexer().parse(case).unwrap()).unwrap();
        let compiled = compile_sk(parsed.into(), &names);

        let result = reduce_dyn(&compiled);

        assert_eq!(decode_sk(&result[0].orient(), &names).to_string(), expected);
    }

    #[test_log::test]
    fn test_eval_id() {
        let case = "((SK)S)";
        let names = Default::default();

        let parsed = parser().parse(lexer().parse(case).unwrap()).unwrap();
        let compiled = compile_sk(parsed.into(), &names);

        let _ = reduce_dyn(&compiled);
    }

    #[test_log::test]
    fn test_eval_id_app_id() {
        let (case, expected) = ("((((SK)S)((SK)S))K)", "K");
        let names = Default::default();

        let parsed = parser().parse(lexer().parse(case).unwrap()).unwrap();
        let compiled = compile_sk(parsed.into(), &names);

        let result = reduce_dyn(&compiled);

        assert_eq!(decode_sk(&result[0].orient(), &names).to_string(), expected);
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

        let _ = compile_icalc(parsed);
    }
}
