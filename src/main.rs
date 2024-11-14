use chumsky::Parser;
use clap::{builder::OsStr, Arg, ArgAction, ArgMatches, Command};
use inetlib::{
    ast::{parser, Expr},
    reducers,
};
use std::{
    fs::OpenOptions,
    io::{Read, Write},
};

fn main() {
    let cmd = clap::Command::new("icc")
        .bin_name("icc")
        .subcommand_required(true)
        .subcommand(
            Command::new("compile")
                .about("Parses an input .inet file, producing a simplified bincode representation in the specified out file")
                .arg(arg_in_file())
                .arg(arg_out_file_default("out.inetcode".into()))
        )
        .subcommand(
            Command::new("simplify")
                .about("Parses an input .inet file, producing a simplified output in the specified out file")
                .arg(arg_out_file_default("out.inet".into()))
        );

    let arg_matches = cmd.get_matches();
    match arg_matches.subcommand() {
        Some(("compile", arg_matches)) => {
            transform_input_to_output(arg_matches, |e: Expr| {
                bincode::serialize(&reducers::simplify_all(e)).expect("failed to serialize output")
            });
        }
        Some(("simplify", arg_matches)) => {
            transform_input_to_output(arg_matches, |e: Expr| {
                reducers::simplify_all(e).to_string().as_bytes().to_vec()
            });
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

    let parsed: Expr = parser().parse(input).expect("failed to parse input");
    let out = transformer(parsed);

    OpenOptions::new()
        .write(true)
        .create(true)
        .open(out_fname)
        .expect("failed to open output file")
        .write_all(out.as_slice())
        .expect("failed to write results to out file");
}

fn arg_in_file() -> Arg {
    Arg::new("source")
        .num_args(1)
        .last(true)
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
