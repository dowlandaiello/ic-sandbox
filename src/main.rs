use ariadne::{Color, Label, Report, ReportKind, Source};
use chumsky::Parser;
use clap::{builder::OsStr, Arg, ArgAction, ArgMatches, Command};
use inetlib::{
    ast::{self, Expr},
    preprocessor, reducers,
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
            Command::new("compile")
                .about("Parses an input .inet file, producing a bincode representation in the specified out file")
                .arg(arg_in_file())
                .arg(arg_out_file_default("out.inetcode".into()))
        )
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
            transform_input_to_output(arg_matches, |e: Expr| {
                bincode::serialize(&e).expect("failed to serialize output")
            });
        }
        Some(("eval", arg_matches)) => {
            transform_input_to_output(arg_matches, |e: Expr| {
                match e
                    .clone()
                    .to_application()
                    .and_then(|(rules, instance)| reducers::build_application_net(rules, instance))
                {
                    Some((rules, instance)) => {
                        reducers::reduce_to_end_or_infinity(&rules, instance)
                            .into_iter()
                            .map(|reduction| reduction.to_string())
                            .collect::<Vec<_>>()
                            .join(", ")
                            .as_bytes()
                            .to_vec()
                    }
                    _ => {
                        panic!("cannot be reduced");
                    }
                }
            });
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
                let in_expr = assert_parse_ok("".into(), ".".into(), input.trim());

                loop {
                    print!("print_net|debug_net|print_ast|debug_ast|reduce|exit > ");

                    io::stdout().flush().unwrap();

                    let mut cmd = String::new();

                    if io::stdin().read_line(&mut cmd).unwrap() == 0 {
                        return;
                    }

                    match cmd.trim() {
                        "print_net" => match in_expr.clone() {
                            Expr::Application { rules, instance } => {
                                let (rule_nets, instance_net) = if let Some(r) =
                                    reducers::build_application_net(rules, instance)
                                {
                                    r
                                } else {
                                    eprintln!("cannot be debugged");

                                    return;
                                };

                                println!(
                                    "{}\n{}",
                                    rule_nets
                                        .into_iter()
                                        .map(|s| format!("{} => {}", s.0, s.1))
                                        .collect::<Vec<_>>()
                                        .join("\n"),
                                    instance_net
                                );
                            }
                            Expr::Book { rules } => {
                                let book_nets = reducers::build_book_net(rules);

                                println!(
                                    "{}",
                                    book_nets
                                        .into_iter()
                                        .map(|s| format!("{} => {}", s.0, s.1))
                                        .collect::<Vec<_>>()
                                        .join("\n")
                                );
                            }
                        },
                        "debug_net" => match in_expr.clone() {
                            Expr::Application { rules, instance } => {
                                let (rule_nets, instance_net) = if let Some(r) =
                                    reducers::build_application_net(rules, instance)
                                {
                                    r
                                } else {
                                    eprintln!("cannot be debugged");

                                    return;
                                };

                                println!("{:?}\n{:?}", rule_nets, instance_net);
                            }
                            Expr::Book { rules } => {
                                let book_nets = reducers::build_book_net(rules);

                                println!("{:?}", book_nets);
                            }
                        },
                        "print_ast" => {
                            println!("{}", in_expr);
                        }
                        "debug_ast" => {
                            println!("{:?}", in_expr);
                        }
                        "reduce" => match in_expr.clone().to_application() {
                            Some((ast_rules, ast_instance)) => {
                                match reducers::build_application_net(
                                    ast_rules.clone(),
                                    ast_instance,
                                ) {
                                    Some((rules, instance)) => {
                                        println!(
                                            "{}",
                                            Expr::Application {
                                                rules: ast_rules.clone(),
                                                instance: reducers::reduce_once(rules, instance)
                                                    .expect("no reduction occurred")
                                            }
                                        );
                                    }
                                    None => eprintln!("cannot be reduced"),
                                }
                            }
                            _ => eprintln!("cannot be reduced"),
                        },
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

fn transform_input_to_output(args: &ArgMatches, transformer: impl Fn(Expr) -> Vec<u8>) {
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

    let parsed: Expr = assert_parse_ok(
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

fn assert_parse_ok(fpath: PathBuf, working_dir: PathBuf, input: &str) -> Expr {
    let input = preprocessor::parser(working_dir, input);

    let errs = match ast::parser().parse(input.as_str()) {
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
        Report::build(ReportKind::Error, (fname, err.span()))
            .with_message(err.to_string())
            .with_label(
                Label::new((fname, err.span()))
                    .with_message(err)
                    .with_color(Color::Red),
            )
            .finish()
            .eprint((fname, Source::from(input.as_str())))
            .unwrap();
    }

    panic!()
}
