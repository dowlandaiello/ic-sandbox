use crate::{
    bytecode::{self, vm::Executor, Program},
    heuristics::{self, TypedProgram},
    parser::parser_lafont::{self, Spanned},
};
use chumsky::{prelude::*, Stream};

pub fn with_typed(program: &str) -> TypedProgram {
    let lexed = parser_lafont::lexer().parse(program).unwrap();
    let parsed = parser_lafont::parser()
        .parse(Stream::from_iter(
            0..program.len(),
            lexed
                .into_iter()
                .flatten()
                .map(|Spanned(v, s)| (Spanned(v, s.clone()), s)),
        ))
        .unwrap();

    let (typed, _) = heuristics::parse_typed_program(parsed);

    typed
}

pub fn with_program(program: &str) -> Program {
    let typed = with_typed(program);

    bytecode::compile(typed)
}

#[test]
pub fn test_reductions() {
    let cases = [(
        "type nat

symbol Z: nat+
symbol S: nat+, nat-
symbol Add: nat-, nat-, nat+

Z() >< Add(x, x)
Z() >< Add(Z(), x)",
        "Z()
Z() >< Add(x, x)",
    )];

    for (case, expected) in cases {
        let bytecode = with_program(case);

        let mut exec = Executor::new(bytecode);
        exec.step_to_end();

        let res = exec.readback();
        assert_eq!(
            res.nets
                .iter()
                .map(|n| n.to_string())
                .collect::<Vec<_>>()
                .join("\n"),
            expected
        );
    }
}

#[test]
pub fn test_num_complex_reductions() {
    let cases = [(
        "type nat

symbol Z: nat+
symbol S: nat+, nat-
symbol Add: nat-, nat-, nat+

Z() >< Add(x, x)
S(Z()) >< Add(x, S(x))
S(Z()) >< Add(Z(), x)",
        "S(Z())
S(Z()) >< Add(x, S(x))
Z() >< Add(x, x)",
    )];

    for (case, expected) in cases {
        let bytecode = with_program(case);

        let mut exec = Executor::new(bytecode);
        exec.step_to_end();

        let res = exec.readback();
        assert_eq!(
            res.nets
                .iter()
                .map(|n| n.to_string())
                .collect::<Vec<_>>()
                .join("\n"),
            expected
        );
    }
}
