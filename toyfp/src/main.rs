use clap::{Arg, Command};
use inetlib::parser::naming::NameIter;
use std::{fs::OpenOptions, io::Write, path::PathBuf};
use toyfplib::compiler;

mod cli;

fn main() {
    tracing_subscriber::fmt::init();

    let arg_sk = Arg::new("sk").long("sk").default_missing_value("false");

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
                .arg(&arg_sk),
        )
        .subcommand(
            Command::new("compile")
                .about("Compiles a DVM interaction combinator program from the input .fp file")
                .arg(cli::arg_in_file())
                .arg(cli::arg_out_file())
                .arg(&arg_sk),
        )
        .subcommand(
            Command::new("dev")
                .about("Initiates an interactive REPL prototyping environment")
                .arg(cli::arg_in_file())
                .arg(cli::arg_out_file())
                .arg(&arg_sk),
        );

    let arg_matches = cmd.get_matches();
    match arg_matches.subcommand() {
        Some(("check", arg_matches)) => {
            let input_fname = arg_matches
                .get_one::<String>("source")
                .expect("missing source file name");

            if arg_matches.get_one::<String>("sk").map(|s| s.as_ref()) == Some("true") {
                let _ = cli::sk::read_program(input_fname);
            }

            let _ = cli::lambda::read_program(input_fname);
        }
        Some(("dev", _)) => {
            if arg_matches.get_one::<String>("sk").map(|s| s.as_ref()) == Some("true") {
                let _ = cli::sk::repl();

                return;
            }

            cli::lambda::repl()
        }
        Some(("compile", arg_matches)) => {
            let input_fname = arg_matches
                .get_one::<String>("source")
                .expect("missing source file name");

            let mut out_fname = PathBuf::from(input_fname);
            out_fname.set_extension("d");

            if arg_matches.get_one::<String>("sk").map(|s| s.as_ref()) == Some("true") {
                let program = cli::sk::read_program(input_fname);
                let compiled = compiler::compile_sk(program, &mut NameIter::default());

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
