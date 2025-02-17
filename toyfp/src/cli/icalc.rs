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
    reducers::combinators::{buffered::adjacency_matrix::ReducerBuilder, Reducer},
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

pub fn compile(f_name: &str) -> Vec<Port> {
    let parsed = read_program(f_name);

    compiler::compile_icalc(parsed)
}

pub fn eval(f_name: &str) -> Vec<Expr> {
    let parsed = read_program(f_name);

    let prog = compiler::compile_icalc(parsed);

    let mut reducer = ReducerBuilder::default()
        .with_init_nets(prog.iter())
        .finish();
    reducer.reduce();

    let res = reducer.readback();
    let exprs = res
        .into_iter()
        .map(|port| compiler::decompile_icalc(port))
        .collect();

    exprs
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
