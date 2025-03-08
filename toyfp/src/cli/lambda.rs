use ariadne::{Color, Label, Report, ReportKind, Source};
use ast_ext::Spanned;
use chumsky::{error::SimpleReason, prelude::*};
use inetlib::reducers::combinators::reduce_dyn;
use rustyline::{error::ReadlineError, DefaultEditor};
use std::{fs::OpenOptions, io::Read, path::PathBuf};
use toyfplib::{
    compiler,
    parser::{self, Stmt, Token},
};

pub fn read_program(in_fname: &str) -> impl Iterator<Item = Stmt> + Clone {
    let mut input = String::new();
    OpenOptions::new()
        .read(true)
        .open(in_fname)
        .expect("failed to open input file")
        .read_to_string(&mut input)
        .expect("failed to read input file");

    let input_path = PathBuf::from(in_fname);

    assert_parse_ok(input_path.clone(), input.trim())
}

pub fn repl() {
    let mut rl = DefaultEditor::new().expect("failed to get readline editor");

    loop {
        let names = Default::default();
        let mut stmts = String::new();

        loop {
            let readline = rl.readline(if stmts.is_empty() { ">> " } else { ".. " });

            match readline {
                Ok(line) => {
                    stmts.push_str(&format!("{}\n", line));

                    // This is an expression, we can parse now
                    if !matches!(
                        parser::lexer().parse(line).unwrap()[1],
                        Spanned(Token::Eq, _)
                    ) {
                        let parsed = assert_parse_literal_ok(stmts.as_str());
                        let combinated = compiler::compile(parsed.clone(), &names);

                        if let Some(reduced) =
                            compiler::decompile(reduce_dyn(&combinated).get(0).unwrap())
                        {
                            println!("{}", reduced);
                        } else {
                            println!(
                                "{}",
                                parsed.map(|x| x.to_string()).collect::<Vec<_>>().join("\n")
                            );
                        }

                        break;
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
}

pub fn assert_parse_ok(fpath: PathBuf, input: &str) -> impl Iterator<Item = Stmt> + Clone {
    let errs: Vec<Simple<char>> = match parser::lexer()
        .parse(parser::preprocessor().parse(input).unwrap())
        .map_err(|e| {
            e.into_iter()
                .map(|e| e.with_label("lexing error"))
                .collect::<Vec<_>>()
        })
        .and_then(|res| {
            println!("{:?}", res);

            parser::parser().parse(res).map_err(|e| {
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
            return v.into_iter().map(|Spanned(x, _)| x);
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

pub fn assert_parse_literal_ok(input: &str) -> impl Iterator<Item = Stmt> + Clone {
    let errs: Vec<Simple<char>> = match parser::lexer()
        .parse(parser::preprocessor().parse(input).unwrap())
        .map_err(|e| {
            e.into_iter()
                .map(|e| e.with_label("lexing error"))
                .collect::<Vec<_>>()
        })
        .and_then(|res| {
            parser::parser().parse(res).map_err(|e| {
                e.into_iter()
                    .map(|e| {
                        Simple::<char>::custom(e.span(), format!("{}", e.map(|x| x.0)))
                            .with_label("parsing error")
                    })
                    .collect::<Vec<_>>()
            })
        }) {
        Ok(v) => {
            return v.into_iter().map(|Spanned(x, _)| x);
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
