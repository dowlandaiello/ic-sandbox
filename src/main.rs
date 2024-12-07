use clap::Command;
use inetlib::reducers::combinators::reduce_dyn;

mod cli;

use cli::*;

fn main() {
    tracing_subscriber::fmt::init();

    let cmd = clap::Command::new("dcc")
        .bin_name("icc")
        .subcommand_required(true)
        .subcommand(
            Command::new("eval")
            .about("Parses an input .d file, reducing the input to completion and echoing the reduced expression, if not out file is specified")
            .arg(arg_in_file())
            .arg(arg_out_file_default("STDOUT".into())))
        .subcommand(
            Command::new("check")
            .about("Parses an input .d file, checking the file for type and syntax correctness")
            .arg(arg_in_file())
            .arg(arg_out_file_default("STDOUT".into()))
        );

    let arg_matches = cmd.get_matches();
    match arg_matches.subcommand() {
        Some(("eval", arg_matches)) => {
            transform_input_to_output_cli(arg_matches, |program| {
                let res = reduce_dyn(&program.nets[0]).expect("failed to reduce net");

                res.iter()
                    .map(|n| n.to_string())
                    .collect::<Vec<_>>()
                    .join("\n")
                    .into_bytes()
            });
        }
        Some(("check", arg_matches)) => {
            let input_fname = arg_matches
                .get_one::<String>("source")
                .expect("missing source file name");

            let _ = read_program(input_fname);
        }
        _ => unreachable!("clap should ensure we don't get here"),
    };
}
