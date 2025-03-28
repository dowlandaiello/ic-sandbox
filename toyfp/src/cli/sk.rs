use ariadne::{Color, Label, Report, ReportKind, Source};
use chumsky::{
    error::{Rich, RichReason},
    Parser,
};
use inetlib::reducers::combinators::reduce_dyn;
use rustyline::{error::ReadlineError, DefaultEditor};
use std::{fs::OpenOptions, io::Read, path::PathBuf};
use toyfplib::{
    compiler,
    parser_sk::{self, Expr, SpannedExpr},
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

    let parsed: Expr = assert_parse_ok(Some(input_path.clone()), input.trim()).into();

    parsed
}

pub fn eval(f_name: &str) -> Expr {
    let parsed = read_program(f_name);
    let names = Default::default();
    let combinated = compiler::compile_sk(parsed.clone(), &names);

    tracing::trace!("job: {}", combinated);

    compiler::decode_sk(&reduce_dyn(&combinated).get(0).unwrap().orient(), &names)
}

pub fn assert_parse_ok(fpath: Option<PathBuf>, input: &str) -> SpannedExpr {
    let fname = fpath
        .as_ref()
        .map(|p| p.file_name().and_then(|fname| fname.to_str()))
        .flatten()
        .unwrap_or("");

    let report_errs = |errs: Vec<Rich<_>>| {
        for err in errs {
            Report::build(ReportKind::Error, (fname, err.span().clone().into_range()))
                .with_message(err.to_string().clone())
                .with_label(
                    Label::new((fname, err.span().into_range()))
                        .with_message(if let Some(label) = err.contexts().next() {
                            format!(
                                "{}: {}",
                                label.0,
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

    let lexed = match parser_sk::lexer().parse(input).into_result().map_err(|e| {
        e.into_iter()
            .map(|e| e.map_token(|e| e.to_string()))
            .collect::<Vec<_>>()
    }) {
        Ok(v) => v,
        Err(e) => {
            report_errs(e);
            panic!()
        }
    };

    let parsed_errs: Result<_, Vec<Rich<_>>> = parser_sk::parser()
        .parse(lexed.as_slice())
        .into_result()
        .map_err(|errs| {
            errs.into_iter()
                .map(|e| e.map_token(|c| c.to_string()))
                .collect::<Vec<_>>()
        })
        .to_owned();

    match parsed_errs {
        Ok(v) => v,
        Err(e) => {
            report_errs(e);

            panic!()
        }
    }
}

pub fn repl() {
    let mut rl = DefaultEditor::new().expect("failed to get readline editor");

    loop {
        let readline = rl.readline(">> ");
        let names = Default::default();

        match readline {
            Ok(line) => {
                let parsed = assert_parse_ok(None, line.as_str());
                let combinated = compiler::compile_sk(parsed.clone().into(), &names);

                tracing::trace!("job: {}", combinated);

                let reduced =
                    compiler::decode_sk(&reduce_dyn(&combinated).get(0).unwrap().orient(), &names);
                println!("{}", reduced);
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
