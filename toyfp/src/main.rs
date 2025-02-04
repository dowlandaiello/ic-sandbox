use clap::{Arg, ArgAction, Command};
use inetlib::parser::naming::NameIter;
use std::{fs::OpenOptions, io::Write, path::PathBuf};
use toyfplib::compiler;

mod cli;

fn main() {
    tracing_subscriber::fmt::init();

    let cmd = clap::Command::new("toyfp")
        .bin_name("toyfp")
        .subcommand_required(true)
        .subcommand(
            Command::new("check")
                .about(
                    "Parses an input .fp file, checking the file for type and syntax correctness",
                )
                .arg(cli::arg_in_file())
                .arg(cli::arg_out_file_default("STDOUT".into()))
                .arg(
                    Arg::new("sk")
                        .long("sk")
                        .short('s')
                        .action(ArgAction::SetTrue)
                        .help("use SK combinators as the input mode"),
                ),
        )
        .subcommand(
            Command::new("compile")
                .about("Compiles a DVM interaction combinator program from the input .fp file")
                .arg(cli::arg_in_file())
                .arg(cli::arg_out_file())
                .arg(
                    Arg::new("sk")
                        .long("sk")
                        .short('s')
                        .action(ArgAction::SetTrue)
                        .help("use SK combinators as the input mode"),
                ),
        )
        .subcommand(
            Command::new("eval")
                .about("Evaluates a DVM interaction combinator program from the input .fp file")
                .arg(cli::arg_in_file())
                .arg(cli::arg_out_file())
                .arg(
                    Arg::new("sk")
                        .long("sk")
                        .short('s')
                        .action(ArgAction::SetTrue)
                        .help("use SK combinators as the input mode"),
                ),
        )
        .subcommand(
            Command::new("dev")
                .about("Initiates an interactive REPL prototyping environment")
                .arg(cli::arg_in_file())
                .arg(cli::arg_out_file())
                .arg(
                    Arg::new("sk")
                        .long("sk")
                        .short('s')
                        .action(ArgAction::SetTrue)
                        .help("use SK combinators as the input mode"),
                ),
        );

    let arg_matches = cmd.get_matches();
    match arg_matches.subcommand() {
        Some(("check", arg_matches)) => {
            let input_fname = arg_matches
                .get_one::<String>("source")
                .expect("missing source file name");

            if arg_matches.get_flag("sk") {
                let _ = cli::sk::read_program(input_fname);
            }

            let _ = cli::lambda::read_program(input_fname);
        }
        Some(("dev", arg_matches)) => {
            if arg_matches.get_flag("sk") {
                let _ = cli::sk::repl();

                return;
            }

            cli::lambda::repl()
        }
        Some(("eval", arg_matches)) => {
            let input_fname = arg_matches
                .get_one::<String>("source")
                .expect("missing source file name");

            if arg_matches.get_flag("sk") {
                let res = cli::sk::eval(input_fname);

                println!("{}", res);

                return;
            }

            todo!()
        }
        Some(("compile", arg_matches)) => {
            let input_fname = arg_matches
                .get_one::<String>("source")
                .expect("missing source file name");

            let mut out_fname = PathBuf::from(input_fname);
            out_fname.set_extension("d");

            if arg_matches.get_flag("sk") {
                let program = cli::sk::read_program(input_fname);
                let compiled = compiler::compile_sk(program);

                let mut out_f = OpenOptions::new()
                    .write(true)
                    .create(true)
                    .open(out_fname)
                    .expect("failed to open compiled .d file");
                out_f
                    .write_all(compiled.to_string().as_bytes())
                    .expect("failed to write compiled combinator program");

                return;
            }

            let program = cli::lambda::read_program(input_fname);
            let compiled = compiler::compile(program, &mut NameIter::default());

            let mut out_f = OpenOptions::new()
                .write(true)
                .create(true)
                .open(out_fname)
                .expect("failed to open compiled .d file");
            out_f
                .write_all(compiled.to_string().as_bytes())
                .expect("failed to write compiled combinator program");
        }
        _ => unreachable!("clap should ensure we don't get here"),
    };
}
