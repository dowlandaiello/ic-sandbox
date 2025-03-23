use clap::{Arg, ArgAction, Command};
use inetlib::reducers::combinators::reduce_dyn;
use std::path::PathBuf;
use toyfplib::compiler;

mod cli;

fn main() {
    tracing_subscriber::fmt::init();

    let flag_combinator = Arg::new("comb")
        .long("combinator")
        .short('c')
        .action(ArgAction::SetTrue)
        .help("use SKBCW combinators as the input mode");

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
                .arg(flag_combinator.clone()),
        )
        .subcommand(
            Command::new("compile")
                .about("Compiles a program from the input .fp file")
                .arg(cli::arg_in_file())
                .arg(cli::arg_out_file())
                .arg(flag_combinator.clone()),
        )
        .subcommand(
            Command::new("eval")
                .about("Evaluates a DVM interaction combinator program from the input .fp file")
                .arg(cli::arg_in_file())
                .arg(cli::arg_out_file())
                .arg(flag_combinator.clone()),
        )
        .subcommand(
            Command::new("dev")
                .about("Initiates an interactive REPL prototyping environment")
                .arg(cli::arg_in_file())
                .arg(cli::arg_out_file())
                .arg(flag_combinator.clone()),
        );

    let arg_matches = cmd.get_matches();
    match arg_matches.subcommand() {
        Some(("check", arg_matches)) => {
            let input_fname = arg_matches
                .get_one::<String>("source")
                .expect("missing source file name");

            if arg_matches.get_flag("comb") {
                let _ = cli::sk::read_program(input_fname);
            }

            let _ = cli::lambda::read_program(input_fname);
        }
        Some(("dev", arg_matches)) => {
            if arg_matches.get_flag("comb") {
                let _ = cli::sk::repl();

                return;
            }

            cli::lambda::repl()
        }
        Some(("eval", arg_matches)) => {
            let input_fname = arg_matches
                .get_one::<String>("source")
                .expect("missing source file name");

            if arg_matches.get_flag("comb") {
                let res = cli::sk::eval(input_fname);

                println!("{}", res);

                return;
            }

            let names = Default::default();

            let prog = cli::lambda::read_program(input_fname);
            let compiled = compiler::compile(prog, &names);

            let reduced =
                compiler::decompile(reduce_dyn(&compiled).get(0).unwrap(), &names).unwrap();

            println!("{}", reduced);
        }
        Some(("compile", arg_matches)) => {
            let input_fname = arg_matches
                .get_one::<String>("source")
                .expect("missing source file name");
            let names = Default::default();

            let mut out_fname = PathBuf::from(input_fname);
            out_fname.set_extension("d");

            if arg_matches.get_flag("comb") {
                let program = cli::sk::read_program(input_fname);
                let compiled = compiler::compile_sk(program, &names);

                println!("{}", compiled);

                return;
            }

            let program = cli::lambda::read_program(input_fname);
            let compiled = compiler::compile(program, &names);

            println!("{}", compiled);
        }
        _ => unreachable!("clap should ensure we don't get here"),
    };
}
