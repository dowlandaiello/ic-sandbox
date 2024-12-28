use ariadne::{Color, Label, Report, ReportKind, Source};
use chumsky::{
    error::{Error, Simple, SimpleReason},
    Parser,
};
use inetlib::{
    bytecode::combinated::CombinatedProgram,
    parser::{
        ast_combinators::{Expr, Port},
        parser_combinators,
    },
};
use std::{
    env::args,
    fs::OpenOptions,
    io::{Read, Write},
    path::PathBuf,
    process::Command,
};

const MAX_AGENTS_PER_ROW: usize = 5;

fn make_doc(nets: Vec<Port>) -> String {
    let fmt_conn_port = |a: &Port, b: &Port| -> Option<String> {
        if a.borrow().is_var() || b.borrow().is_var() {
            return None;
        }

        let port_a = a.wire_position(b)?;

        let port_b = b.wire_position(a)?;

        let port_fmt_a = match port_a {
            0 => String::from("pal 1"),
            n => format!("pax {}", n),
        };
        let port_fmt_b = match port_b {
            0 => String::from("pal 1"),
            n => format!("pax {}", n),
        };

        Some(format!(
            "\\inetwire({}.{})({}.{})",
            a.id, port_fmt_a, b.id, port_fmt_b,
        ))
    };

    let nodes = nets
        .iter()
        .map(|p| p.iter_tree())
        .flatten()
        .enumerate()
        .filter_map(|(i, p)| match &*p.borrow() {
            &Expr::Era(_) => Some(format!(
                "\\inetmulticell({}){{$\\varepsilon$}}{{1}}{{0}}{{{}, {}}}[U]
\\inetport({}.pal 1)",
                p.id,
                i % MAX_AGENTS_PER_ROW,
                i / MAX_AGENTS_PER_ROW,
                p.id,
            )),
            &Expr::Constr(_) => Some(format!(
                "\\inetmulticell({}){{$\\gamma$}}{{1}}{{2}}{{{}, {}}}[U]
\\inetport({}.pal 1)
\\inetport({}.pax 1)
\\inetport({}.pax 2)",
                p.id,
                i % MAX_AGENTS_PER_ROW,
                i / MAX_AGENTS_PER_ROW,
                p.id,
                p.id,
                p.id
            )),
            &Expr::Dup(_) => Some(format!(
                "\\inetmulticell({}){{$\\delta$}}{{1}}{{2}}{{{}, {}}}[U]
\\inetport({}.pal 1)
\\inetport({}.pax 1)
\\inetport({}.pax 2)",
                p.id,
                i % MAX_AGENTS_PER_ROW,
                i / MAX_AGENTS_PER_ROW,
                p.id,
                p.id,
                p.id
            )),
            Expr::Var(_) => None,
        })
        .collect::<Vec<_>>();
    let wires = nets
        .iter()
        .map(|p| p.iter_tree())
        .flatten()
        .map(|p| {
            [p.borrow().primary_port().cloned()]
                .into_iter()
                .chain(
                    p.borrow()
                        .aux_ports()
                        .into_iter()
                        .cloned()
                        .collect::<Vec<_>>(),
                )
                .filter(|other| {
                    other
                        .as_ref()
                        .map(|o| o.borrow().is_agent())
                        .unwrap_or_default()
                })
                .filter_map(|other| Some((p.clone(), other?)))
                .collect::<Vec<_>>()
        })
        .flatten()
        .filter_map(|(a, b)| fmt_conn_port(&a, &b))
        .collect::<Vec<_>>();
    format!(
        "\\documentclass{{minimal}}
\\usepackage{{tikz-multinets}}
\\begin{{document}}
\\begin{{tikzpicture}}
{}
{}
\\end{{tikzpicture}}
\\end{{document}}",
        nodes
            .into_iter()
            .map(|s| s.to_string())
            .collect::<Vec<_>>()
            .join("\n"),
        wires
            .into_iter()
            .map(|s| s.to_string())
            .collect::<Vec<_>>()
            .join("\n"),
    )
}

fn main() {
    let input_fname = args()
        .last()
        .map(|a| PathBuf::from(a))
        .expect("missing input file src");

    let mut f = OpenOptions::new()
        .read(true)
        .open(&input_fname)
        .expect("could not open input file");
    let mut cts = String::new();
    f.read_to_string(&mut cts)
        .expect("could not read input file");

    let program = assert_parse_ok(input_fname, &cts);

    let doc = make_doc(program.nets);

    println!("{}", doc);

    let mut out = OpenOptions::new()
        .write(true)
        .create(true)
        .open("out.tex")
        .expect("could not open out file");
    out.write_all(doc.as_bytes())
        .expect("could not write to out file");

    Command::new("pdflatex").arg("out.tex").output().unwrap();
}

pub fn assert_parse_ok(fpath: PathBuf, input: &str) -> CombinatedProgram {
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
            .eprint((fname, Source::from(input)))
            .unwrap();
    }

    panic!()
}
