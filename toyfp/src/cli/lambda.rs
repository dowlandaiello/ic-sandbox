use ariadne::{Color, Label, Report, ReportKind, Source};
use ast_ext::Spanned;
use chumsky::{error::RichReason, prelude::*};
use inetlib::reducers::combinators::reduce_dyn;
use rustyline::{error::ReadlineError, DefaultEditor};
use std::{fs::OpenOptions, io::Read, path::PathBuf};
use toyfplib::{
    compiler,
    parser::{self, Stmt, Token},
};

pub fn read_program(in_fname: &str) -> impl Iterator<Item = Spanned<Stmt>> + Clone {
    let mut input = String::new();
    OpenOptions::new()
        .read(true)
        .open(in_fname)
        .expect("failed to open input file")
        .read_to_string(&mut input)
        .expect("failed to read input file");

    let input_path = PathBuf::from(in_fname);

    assert_parse_ok(Some(input_path.clone()), input.trim())
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
                        parser::lexer().parse(&line).unwrap().get(1),
                        Some(Spanned(Token::Eq, _))
                    ) {
                        let parsed = assert_parse_ok(None, stmts.as_str());
                        let combinated = compiler::compile(parsed.clone(), &names);

                        let reduced =
                            compiler::decompile(reduce_dyn(&combinated).get(0).unwrap(), &names)
                                .unwrap();

                        println!("{}", reduced);

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

pub fn assert_parse_ok(
    fpath: Option<PathBuf>,
    input: &str,
) -> impl Iterator<Item = Spanned<Stmt>> + Clone {
    let unwrap_errs = |errs: Vec<Rich<_>>| {
        let fname = fpath
            .as_ref()
            .and_then(|p| p.file_name().and_then(|fname| fname.to_str()))
            .unwrap_or("");

        for err in errs {
            Report::build(ReportKind::Error, (fname, err.span().clone().into_range()))
                .with_message(err.to_string().clone())
                .with_label(
                    Label::new((fname, err.span().into_range()))
                        .with_message(if let Some(label) = err.contexts().next() {
                            format!(
                                "{}:{}: {}",
                                label.0,
                                label.1,
                                if let RichReason::Custom(s) = err.reason() {
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
    };

    let preprocessed_1 = fpath
        .as_ref()
        .map(|p| ast_ext::preprocess(input, p.into()))
        .unwrap_or(input.to_string());

    let lexed = match parser::lexer()
        .parse(&preprocessed_1)
        .into_result()
        .map_err(|e| {
            e.into_iter()
                .map(|e| e.map_token(|c| c.to_string()))
                .collect::<Vec<_>>()
        }) {
        Ok(v) => v,
        Err(e) => {
            unwrap_errs(e);
            panic!()
        }
    };

    match parser::parser()
        .parse(&lexed)
        .into_result()
        .map_err(|e| {
            e.into_iter()
                .map(|c| c.map_token(|c| c.to_string()))
                .collect::<Vec<_>>()
        })
        .map(|x| x.into_iter())
    {
        Ok(v) => {
            return v;
        }
        Err(e) => {
            unwrap_errs(e);

            panic!()
        }
    };
}
