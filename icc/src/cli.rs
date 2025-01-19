use ariadne::{Color, Label, Report, ReportKind, Source};
use chumsky::{
    error::{Error, Simple, SimpleReason},
    Parser,
};
use clap::{builder::OsStr, Arg, ArgAction, ArgMatches};
use inetlib::{
    heuristics::{self, TypedProgram},
    parser::parser_lafont::{self},
    preprocessor, BYTECODE_EXTENSION,
};
use std::{
    fs::OpenOptions,
    io::{Read, Write},
    path::PathBuf,
};

pub fn compile(args: &ArgMatches, transformer: impl Fn(TypedProgram) -> Vec<u8>) {
    let input_fname = args
        .get_one::<String>("source")
        .expect("missing source file name");
    let mut out_fname = input_fname.split_terminator(".i").collect::<String>();
    out_fname.push_str(BYTECODE_EXTENSION);

    transform_input_to_output(input_fname, &out_fname, transformer)
}

pub fn transform_input_to_output_cli(
    args: &ArgMatches,
    transformer: impl Fn(TypedProgram) -> Vec<u8>,
) {
    let out_fname = args
        .get_one::<String>("out")
        .expect("missing output file name");
    let input_fname = args
        .get_one::<String>("source")
        .expect("missing source file name");

    transform_input_to_output(input_fname, out_fname, transformer)
}

pub fn transform_input_to_output(
    in_fname: &str,
    out_fname: &str,
    transformer: impl Fn(TypedProgram) -> Vec<u8>,
) {
    let mut input = String::new();
    OpenOptions::new()
        .read(true)
        .open(in_fname)
        .expect("failed to open input file")
        .read_to_string(&mut input)
        .expect("failed to read input file");

    let input_path = PathBuf::from(in_fname);

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

pub fn assert_parse_ok(fpath: PathBuf, working_dir: PathBuf, input: &str) -> TypedProgram {
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
                            Simple::<char>::custom(
                                e.found().unwrap().1.clone(),
                                format!("{}", e.map(|x| x.0)),
                            )
                            .with_label("parsing error")
                        })
                        .collect::<Vec<_>>()
                })
                .and_then(|res| {
                    let (output, errors) = heuristics::parse_typed_program(res);

                    if !errors.is_empty() {
                        Err(errors
                            .into_iter()
                            .map(|e| {
                                Simple::<char>::custom(
                                    e.span(),
                                    match e.reason() {
                                        SimpleReason::Custom(s) => s.to_string(),
                                        _ => unreachable!(),
                                    },
                                )
                                .with_label("typing error")
                            })
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
