use ariadne::{Color, Label, Report, ReportKind, Source};
use chumsky::{
    error::{Error, Simple, SimpleReason},
    Parser,
};
use clap::{builder::OsStr, Arg, ArgAction, ArgMatches};
use inetlib::{
    bytecode::combinated::CombinatedProgram,
    parser::{
        naming::NameIter,
        parser_combinators::{self},
    },
    preprocessor,
    reducers::combinators::{
        buffered::adjacency_matrix::{BufferedMatrixReducer, ReducerBuilder},
        Reducer,
    },
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
    sync::Arc,
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
                let mut parsed = assert_parse_literal_ok(line.as_str());

                loop {
                    let cmd = rl.readline(&format!(
                        "[{}...] (step|reduce|print|exit) >> ",
                        &parsed.to_string().chars().take(10).collect::<String>()
                    ));

                    match cmd.as_ref().map(|s| s.as_str()) {
                        Ok("exit") | Err(ReadlineError::Eof) => {
                            break;
                        }
                        Ok("print") => {
                            println!("{}", parsed);
                        }
                        Ok("step") => {
                            let names = Arc::new(NameIter::default());

                            let (rx, builder) = ReducerBuilder::new_in_redex_loop();
                            let reducer = builder.with_init_net(parsed.nets[0]).finish();

                            let next = rx.recv().unwrap();

                            let res = reducer.reduce_step(next);

                            println!(
                                "{}",
                                res.nets
                                    .iter()
                                    .map(|n| n.to_string())
                                    .collect::<Vec<_>>()
                                    .join("\n")
                            );
                        }
                        Ok("reduce") => {
                            let reducer = BufferedMatrixReducer::from(parsed.nets.remove(0));
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
    transformer: impl Fn(CombinatedProgram) -> Vec<u8>,
) {
    let out_fname = args
        .get_one::<String>("out")
        .expect("missing output file name");
    let input_fname = args
        .get_one::<String>("source")
        .expect("missing source file name");

    transform_input_to_output(input_fname, out_fname, transformer)
}

pub fn read_program(in_fname: &str) -> CombinatedProgram {
    let mut input = String::new();
    OpenOptions::new()
        .read(true)
        .open(in_fname)
        .expect("failed to open input file")
        .read_to_string(&mut input)
        .expect("failed to read input file");

    let input_path = PathBuf::from(in_fname);

    let parsed: CombinatedProgram = assert_parse_ok(
        input_path.clone(),
        input_path
            .ancestors()
            .nth(1)
            .expect("failed to get working dir for file")
            .to_path_buf(),
        input.trim(),
    );

    parsed
}

pub fn transform_input_to_output(
    in_fname: &str,
    out_fname: &str,
    transformer: impl Fn(CombinatedProgram) -> Vec<u8>,
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

fn assert_parse_literal_ok(input: &str) -> CombinatedProgram {
    let errs: Vec<Simple<char>> = match parser_combinators::lexer()
        .parse(input)
        .map_err(|e| {
            e.into_iter()
                .map(|e| e.with_label("lexing error"))
                .collect::<Vec<_>>()
        })
        .and_then(|res| {
            parser_combinators::parser().parse(res).map_err(|e| {
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
            return CombinatedProgram {
                nets: v.into_iter().map(|x| x.0).collect(),
            };
        }
        Err(e) => e,
    };

    let fname = "<repl>";

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

pub fn assert_parse_ok(fpath: PathBuf, working_dir: PathBuf, input: &str) -> CombinatedProgram {
    let input = preprocessor::parser(working_dir, input);

    let errs: Vec<Simple<char>> = match parser_combinators::lexer()
        .parse(input.as_str())
        .map_err(|e| {
            e.into_iter()
                .map(|e| e.with_label("lexing error"))
                .collect::<Vec<_>>()
        })
        .and_then(|res| {
            parser_combinators::parser().parse(res).map_err(|e| {
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
            return CombinatedProgram {
                nets: v.into_iter().map(|x| x.0).collect(),
            };
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
            .eprint((fname, Source::from(input.as_str())))
            .unwrap();
    }

    panic!()
}
