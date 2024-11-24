use ariadne::{Color, Label, Report, ReportKind, Source};
use chumsky::{
    error::{Error, Simple},
    Parser,
};
use clap::{builder::OsStr, Arg, ArgAction, ArgMatches, Command};
use inetlib::{
    heuristics::{self, TypedProgram},
    parser_lafont::{self},
    preprocessor,
};
use std::{
    fs::OpenOptions,
    io::{self, Read, Write},
    path::PathBuf,
};

fn main() {
    tracing_subscriber::fmt::init();

    let cmd = clap::Command::new("icc")
        .bin_name("icc")
        .subcommand_required(true)
        .subcommand(
            Command::new("eval")
            .about("Parses an input .inet file, reducing the input to completion and echoing the reduced expression, if not out file is specified")
            .arg(arg_in_file())
            .arg(arg_out_file_default("STDOUT".into())
        ))
        .subcommand(
            Command::new("dev")
            .about("Interactively evaluates interaction nets")
        );

    let arg_matches = cmd.get_matches();
    match arg_matches.subcommand() {
        Some(("compile", arg_matches)) => {
            transform_input_to_output(arg_matches, |_e| todo!());
        }
        Some(("eval", arg_matches)) => {
            transform_input_to_output(arg_matches, |_e| todo!());
        }
        Some(("dev", _)) => {
            loop {
                let mut input = String::new();

                loop {
                    print!("> ");
                    io::stdout().flush().unwrap();

                    let n_chars_read = io::stdin().read_line(&mut input).unwrap();

                    if n_chars_read == 0 {
                        return;
                    }

                    if input.ends_with("\n\n") {
                        break;
                    }
                }

                // Try parsing input as an expr
                let _ = assert_parse_ok("".into(), ".".into(), input.trim());

                loop {
                    print!("print_net|debug_net|print_ast|debug_ast|reduce|exit > ");

                    io::stdout().flush().unwrap();

                    let mut cmd = String::new();

                    if io::stdin().read_line(&mut cmd).unwrap() == 0 {
                        return;
                    }

                    match cmd.trim() {
                        "print_net" => todo!(),
                        "debug_net" => todo!(),
                        "print_ast" => {
                            todo!()
                        }
                        "debug_ast" => {
                            todo!()
                        }
                        "reduce" => { /*match in_expr.clone().to_application() {
                                 Some((ast_rules, ast_instance)) => {
                                     match reducers::naive::build_application_net(
                                         ast_rules.clone(),
                                         ast_instance,
                                     ) {
                                         Some((rules, instance)) => {
                                             println!(
                                                 "{}",
                                                 Expr::Application {
                                                     rules: ast_rules.clone(),
                                                     instance: reducers::naive::reduce_once(
                                                         rules, instance
                                                     )
                                                     .expect("no reduction occurred")
                                                 }
                                             );
                                         }
                                         None => eprintln!("cannot be reduced"),
                                     }
                                 }
                                 _ => eprintln!("cannot be reduced"),
                             }*/
                        }
                        "exit" => {
                            break;
                        }
                        _ => {}
                    }
                }
            }
        }
        _ => unreachable!("clap should ensure we don't get here"),
    };
}

fn transform_input_to_output(args: &ArgMatches, transformer: impl Fn(TypedProgram) -> Vec<u8>) {
    let out_fname = args
        .get_one::<String>("out")
        .expect("missing output file name");
    let input_fname = args
        .get_one::<String>("source")
        .expect("missing source file name");

    let mut input = String::new();
    OpenOptions::new()
        .read(true)
        .open(input_fname)
        .expect("failed to open input file")
        .read_to_string(&mut input)
        .expect("failed to read input file");

    let input_path = PathBuf::from(input_fname);

    let parsed: TypedProgram = assert_parse_ok(
        input_path.clone(),
        input_path
            .ancestors()
            .nth(1)
            .expect("failed to get working dir for file")
            .to_path_buf(),
        input.trim(),
    );
    let out = transformer(parsed);

    match out_fname.as_str() {
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

fn arg_in_file() -> Arg {
    Arg::new("source")
        .value_name("SOURCE")
        .require_equals(true)
        .action(ArgAction::Set)
}

fn arg_out_file_default(default: OsStr) -> Arg {
    Arg::new("out")
        .short('o')
        .long("out")
        .value_name("OUT")
        .require_equals(true)
        .default_value(default)
        .action(ArgAction::Set)
}

fn assert_parse_ok(fpath: PathBuf, working_dir: PathBuf, input: &str) -> TypedProgram {
    let input = preprocessor::parser(working_dir, input);

    let errs: Vec<Simple<char>> = match parser_lafont::lexer()
        .parse(input.as_str())
        .map_err(|e| {
            e.into_iter()
                .map(|e| e.with_label("lexing error"))
                .collect::<Vec<_>>()
        })
        .and_then(|res| {
            parser_lafont::parser()
                .parse(res.into_iter().flatten().collect::<Vec<_>>())
                .map_err(|e| {
                    e.into_iter()
                        .map(|e| {
                            e.map(|s| s.0.to_string().chars().next().unwrap())
                                .with_label("parsing error")
                        })
                        .collect::<Vec<_>>()
                })
                .and_then(|res| {
                    let (output, errors) = heuristics::parse_typed_program(res);

                    if !errors.is_empty() {
                        Err(errors
                            .into_iter()
                            .map(|e| e.with_label("typing error"))
                            .collect::<Vec<_>>())
                    } else {
                        Ok(output)
                    }
                })
        }) {
        Ok(v) => {
            return v;
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
                        format!("{}: {}", label, err.to_string())
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
