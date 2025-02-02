pub mod icalc;
pub mod lambda;
pub mod sk;

use clap::{builder::OsStr, Arg, ArgAction};

pub fn arg_in_file() -> Arg {
    Arg::new("source")
        .value_name("SOURCE")
        .require_equals(true)
        .action(ArgAction::Set)
}

pub fn arg_out_file() -> Arg {
    Arg::new("out")
        .value_name("OUT")
        .require_equals(false)
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
