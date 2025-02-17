use ariadne::{Color, Label, Report, ReportKind, Source};
use chumsky::{
    error::{Error, Simple, SimpleReason},
    Parser,
};
use inetlib::{
    parser::{
        ast_combinators::{Constructor, Expr as CExpr, Port, Var},
        ast_lafont::Ident,
        naming::NameIter,
    },
    reducers::combinators::buffered::adjacency_matrix::ReducerBuilder,
};
use rustyline::{error::ReadlineError, DefaultEditor};
use std::{collections::BTreeMap, fs::OpenOptions, io::Read, path::PathBuf};
use toyfplib::{
    compiler,
    parser_icalc::{self, Abstraction, Application, Definition, Duplication, Expr, Stmt},
};

pub fn read_program(in_fname: &str) -> Vec<Stmt> {
    let mut input = String::new();
    OpenOptions::new()
        .read(true)
        .open(in_fname)
        .expect("failed to open input file")
        .read_to_string(&mut input)
        .expect("failed to read input file");

    let input_path = PathBuf::from(in_fname);

    let parsed: Vec<Stmt> = assert_parse_ok(input_path.clone(), input.trim());

    parsed
}

pub fn eval(f_name: &str) -> Vec<Expr> {
    let parsed = read_program(f_name);

    let mut names = NameIter::default();

    fn cc_expr(e: &Expr, names: &mut NameIter) -> Port {
        match e {
            Expr::Abstraction(Abstraction { bind_var, body }) => {
                let body_cc = cc_expr(&body, names);
                let var_cc = CExpr::Var(Var {
                    name: Ident(bind_var.to_string()),
                    port: None,
                })
                .into_port(names);

                let lam = CExpr::Constr(Constructor {
                    primary_port: None,
                    aux_ports: [Some((0, body_cc)), Some((0, var_cc))],
                })
                .into_port(names);

                var_cc.borrow_mut().set_primary_port(Some((2, lam.clone())));
                body_cc
                    .borrow_mut()
                    .set_primary_port(Some((1, lam.clone())));

                lam
            }
            Expr::Application(Application(lhs, rhs)) => {
                let lhs_cc = cc_expr(lhs, names);
                let rhs_cc = cc_expr(rhs, names);

                lhs_cc
                    .borrow_mut()
                    .set_primary_port(Some((0, rhs_cc.clone())));
                rhs_cc
                    .borrow_mut()
                    .set_primary_port(Some((0, lhs_cc.clone())));

                lhs_cc
            }
            Expr::Duplication(Duplication {
                pair,
                to_clone,
                in_expr,
            }) => {}
        }
    };

    let lookup_table: BTreeMap<&str, Port> = parsed.iter().map(|stmt| match stmt {
        Stmt::Def(Definition { name, definition }) => {
            todo!()
        }
    });

    let reducer = ReducerBuilder::default().with_init_nets();
}

pub fn assert_parse_ok(fpath: PathBuf, input: &str) -> Vec<Stmt> {
    let errs: Vec<Simple<char>> = match parser_icalc::lexer()
        .parse(input)
        .map_err(|e| {
            e.into_iter()
                .map(|e| e.with_label("lexing error"))
                .collect::<Vec<_>>()
        })
        .and_then(|res| {
            parser_icalc::parser()
                .parse(res.into_iter().flatten().collect::<Vec<_>>())
                .map_err(|e| {
                    e.into_iter()
                        .map(|e| {
                            Simple::<char>::custom(
                                e.found().unwrap().1.clone(),
                                format!("{}", e.map(|x| x.0)),
                            )
                            .with_label("parsing error")
                        })
                        .collect::<Vec<_>>()
                })
        }) {
        Ok(v) => {
            return v.into_iter().map(|x| x.0).collect();
        }
        Err(e) => e,
    };

    let fname = fpath
        .file_name()
        .and_then(|fname| fname.to_str())
        .unwrap_or("");

    for err in errs {
        Report::build(ReportKind::Error, (fname, err.span().clone()))
            .with_message(err.to_string().clone())
            .with_label(
                Label::new((fname, err.span()))
                    .with_message(if let Some(label) = err.label() {
                        format!(
                            "{}: {}",
                            label,
                            if let SimpleReason::Custom(s) = err.reason() {
                                s.to_string()
                            } else {
                                err.to_string()
                            }
                        )
                    } else {
                        err.to_string()
                    })
                    .with_color(Color::Red),
            )
            .finish()
            .eprint((fname, Source::from(input)))
            .unwrap();
    }

    panic!()
}

pub fn assert_parse_literal_ok(input: &str) -> Vec<Stmt> {
    let errs: Vec<Simple<char>> = match parser_icalc::lexer()
        .parse(input)
        .map_err(|e| {
            e.into_iter()
                .map(|e| e.with_label("lexing error"))
                .collect::<Vec<_>>()
        })
        .and_then(|res| {
            parser_icalc::parser()
                .parse(res.into_iter().flatten().collect::<Vec<_>>())
                .map_err(|e| {
                    e.into_iter()
                        .map(|e| {
                            Simple::<char>::custom(e.span(), format!("{}", e.map(|x| x.0)))
                                .with_label("parsing error")
                        })
                        .collect::<Vec<_>>()
                })
        }) {
        Ok(v) => {
            return v.into_iter().map(|x| x.0).collect();
        }
        Err(e) => e,
    };

    let fname = "<STDIN>";

    for err in errs {
        Report::build(ReportKind::Error, (fname, err.span().clone()))
            .with_message(err.to_string().clone())
            .with_label(
                Label::new((fname, err.span()))
                    .with_message(if let Some(label) = err.label() {
                        format!(
                            "{}: {}",
                            label,
                            if let SimpleReason::Custom(s) = err.reason() {
                                s.to_string()
                            } else {
                                err.to_string()
                            }
                        )
                    } else {
                        err.to_string()
                    })
                    .with_color(Color::Red),
            )
            .finish()
            .eprint((fname, Source::from(input)))
            .unwrap();
    }

    panic!()
}

pub fn repl() {
    let mut rl = DefaultEditor::new().expect("failed to get readline editor");

    loop {
        let readline = rl.readline(">> ");

        match readline {
            Ok(line) => {
                let parsed = assert_parse_literal_ok(line.as_str());
                let combinated = todo!();

                todo!()
            }
            Err(ReadlineError::Interrupted) => {
                return;
            }
            Err(ReadlineError::Eof) => {
                return;
            }
            Err(err) => {
                eprintln!("Error: {:?}", err);

                return;
            }
        }
    }
}
