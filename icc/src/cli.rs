use ariadne::{Color, Label, Report, ReportKind, Source};
use chumsky::{
    error::{Rich, RichReason},
    Parser,
};
use clap::{builder::OsStr, Arg, ArgAction, ArgMatches};
use inetlib::{
    parser::{
        ast_combinators::Port,
        parser_combinators::{self},
    },
    reducers::combinators::{buffered::adjacency_matrix::ReducerBuilder, Reducer},
};
use rustyline::{
    completion::Completer, error::ReadlineError, hint::Hinter, history::DefaultHistory, Context,
    Editor, Helper, Highlighter, Validator,
};
use std::{
    collections::BTreeSet,
    default,
    fs::OpenOptions,
    io::{Read, Write},
    path::PathBuf,
};

#[derive(Helper, Validator, Highlighter)]
pub struct KeywordCompleter {
    hints: BTreeSet<&'static str>,
}

impl default::Default for KeywordCompleter {
    fn default() -> Self {
        Self {
            hints: BTreeSet::from_iter(["Constr[", "Era[", "Dup["]),
        }
    }
}

impl Completer for KeywordCompleter {
    type Candidate = String;
}

impl Hinter for KeywordCompleter {
    type Hint = String;

    fn hint(&self, line: &str, _pos: usize, _ctx: &Context<'_>) -> Option<Self::Hint> {
        if line.trim().ends_with(")") && !line.contains("><") {
            if line.ends_with(" ") {
                return Some(">< ".into());
            } else {
                return Some(" >< ".into());
            }
        }

        let digits = line
            .rfind("[@")
            .and_then(|w_pos| Some((w_pos, line[w_pos..].rfind("]")?)))
            .map(|(w_start, w_end)| &line[w_start..(w_start + w_end)])
            .map(|w| w[2..].parse::<usize>().ok())
            .unwrap_or_default();
        let last_word: &str = line.split(" ").last().unwrap_or_default();

        self.hints
            .iter()
            .filter(|hint| hint.starts_with(last_word) && !last_word.is_empty())
            .map(|h| &h[last_word.len()..])
            .next()
            .map(|h| {
                format!(
                    "{}@{}](",
                    h,
                    (digits.iter().max().unwrap_or(&0) + 1) as usize
                )
            })
    }
}

pub fn repl() {
    let mut rl =
        Editor::<KeywordCompleter, DefaultHistory>::new().expect("failed to get readline editor");
    rl.set_helper(Some(KeywordCompleter::default()));

    loop {
        let readline = rl.readline(">> ");

        match readline {
            Ok(line) => {
                let parsed = assert_parse_ok(None, line.as_str());

                loop {
                    let cmd = rl.readline(&format!(
                        "[{}...] (step|reduce|print|exit) >> ",
                        &parsed[0].to_string().chars().take(10).collect::<String>()
                    ));

                    match cmd.as_ref().map(|s| s.as_str()) {
                        Ok("exit") | Err(ReadlineError::Eof) => {
                            break;
                        }
                        Ok("print") => {
                            println!(
                                "{}",
                                parsed
                                    .iter()
                                    .map(|x| x.to_string())
                                    .collect::<Vec<_>>()
                                    .join("\n")
                            );
                        }
                        Ok("step") => {
                            todo!()
                        }
                        Ok("reduce") => {
                            let mut reducer = ReducerBuilder::default()
                                .with_init_nets([&parsed[0]].into_iter())
                                .finish();
                            let res = reducer.reduce();

                            println!(
                                "{}",
                                res.iter()
                                    .map(|n| n.to_string())
                                    .collect::<Vec<_>>()
                                    .join("\n")
                            );
                        }
                        Err(ReadlineError::Interrupted) => {
                            return;
                        }
                        _ => {}
                    }
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

pub fn transform_input_to_output_cli(
    args: &ArgMatches,
    transformer: impl Fn(Vec<Port>) -> Vec<u8>,
) {
    let out_fname = args
        .get_one::<String>("out")
        .expect("missing output file name");
    let input_fname = args
        .get_one::<String>("source")
        .expect("missing source file name");

    transform_input_to_output(input_fname, out_fname, transformer)
}

pub fn read_program(in_fname: &str) -> Vec<Port> {
    let mut input = String::new();
    OpenOptions::new()
        .read(true)
        .open(in_fname)
        .expect("failed to open input file")
        .read_to_string(&mut input)
        .expect("failed to read input file");

    let input_path = PathBuf::from(in_fname);

    let parsed = assert_parse_ok(Some(input_path.clone()), input.trim());

    parsed
}

pub fn transform_input_to_output(
    in_fname: &str,
    out_fname: &str,
    transformer: impl Fn(Vec<Port>) -> Vec<u8>,
) {
    let parsed = read_program(in_fname);
    let out = transformer(parsed);

    match out_fname {
        "STDOUT" => {
            println!("{}", String::from_utf8(out).expect("invalid utf-8 string"));
        }
        out_fname => {
            OpenOptions::new()
                .write(true)
                .create(true)
                .open(out_fname)
                .expect("failed to open output file")
                .write_all(out.as_slice())
                .expect("failed to write results to out file");
        }
    }
}

pub fn arg_in_file() -> Arg {
    Arg::new("source")
        .value_name("SOURCE")
        .require_equals(true)
        .action(ArgAction::Set)
}

pub fn arg_out_file_default(default: OsStr) -> Arg {
    Arg::new("out")
        .short('o')
        .long("out")
        .value_name("OUT")
        .require_equals(true)
        .default_value(default)
        .action(ArgAction::Set)
}

pub fn assert_parse_ok(fpath: Option<PathBuf>, input: &str) -> Vec<Port> {
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

    let lexed = match parser_combinators::lexer()
        .parse(input)
        .into_result()
        .map_err(|e| {
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

    let parsed_errs: Result<_, Vec<Rich<_>>> = parser_combinators::parser()
        .parse(lexed.as_slice())
        .into_result()
        .map_err(|errs| {
            errs.into_iter()
                .map(|e| e.map_token(|c| c.to_string()))
                .collect::<Vec<_>>()
        })
        .to_owned();

    match parsed_errs {
        Ok(v) => v.into_iter().map(|p| p.0).collect(),
        Err(e) => {
            report_errs(e);

            panic!()
        }
    }
}
