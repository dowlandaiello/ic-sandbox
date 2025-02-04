use ariadne::{Color, Label, Report, ReportKind, Source};
use chumsky::{
    error::{Error, Simple, SimpleReason},
    Parser,
};
use inetlib::reducers::combinators::reduce_dyn;
use rustyline::{error::ReadlineError, DefaultEditor};
use std::{fs::OpenOptions, io::Read, path::PathBuf};
use toyfplib::{
    compiler,
    parser_sk::{self, Expr},
};

pub fn read_program(in_fname: &str) -> Expr {
    let mut input = String::new();
    OpenOptions::new()
        .read(true)
        .open(in_fname)
        .expect("failed to open input file")
        .read_to_string(&mut input)
        .expect("failed to read input file");

    let input_path = PathBuf::from(in_fname);

    let parsed: Expr = assert_parse_ok(input_path.clone(), input.trim());

    parsed
}

pub fn eval(f_name: &str) -> Expr {
    let parsed = read_program(f_name);
    let combinated = compiler::compile_sk(parsed.clone());

    tracing::trace!("job: {}", combinated);

    reduce_dyn(&combinated)
        .map(|res| compiler::decode_sk(&res.get(0).unwrap().orient()))
        .expect("reduction failed")
}

pub fn assert_parse_ok(fpath: PathBuf, input: &str) -> Expr {
    let errs: Vec<Simple<char>> = match parser_sk::lexer()
        .parse(input)
        .map_err(|e| {
            e.into_iter()
                .map(|e| e.with_label("lexing error"))
                .collect::<Vec<_>>()
        })
        .and_then(|res| {
            parser_sk::parser().parse(res).map_err(|e| {
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
            return v.into();
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

pub fn assert_parse_literal_ok(input: &str) -> Expr {
    let errs: Vec<Simple<char>> = match parser_sk::lexer()
        .parse(input)
        .map_err(|e| {
            e.into_iter()
                .map(|e| e.with_label("lexing error"))
                .collect::<Vec<_>>()
        })
        .and_then(|res| {
            parser_sk::parser().parse(res).map_err(|e| {
                e.into_iter()
                    .map(|e| {
                        Simple::<char>::custom(e.span(), format!("{}", e.map(|x| x.0)))
                            .with_label("parsing error")
                    })
                    .collect::<Vec<_>>()
            })
        }) {
        Ok(v) => {
            return v.into();
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
                let combinated = compiler::compile_sk(parsed.clone());

                tracing::trace!("job: {}", combinated);

                if let Some(reduced) = reduce_dyn(&combinated)
                    .map(|res| compiler::decode_sk(&res.get(0).unwrap().orient()))
                {
                    println!("{}", reduced);
                } else {
                    println!("{}", parsed);
                }
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
