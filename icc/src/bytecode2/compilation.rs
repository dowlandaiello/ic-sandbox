use super::{GlobalPtr, Op, Program, Ptr, StackElem};
use crate::{
    bytecode2 as bc,
    heuristics::TypedProgram,
    parser::ast_lafont::{Agent, Net, Port},
};
use itertools::Itertools;
use std::{collections::BTreeMap, error, fmt, ptr};

#[derive(Copy, Clone, Debug)]
pub enum Error {
    /// Nets must all be active pairs in LaFont's syntax
    IllFormedNet,

    /// Programs must contain symbol declarations for all agents
    MissingSymbolDeclaration,

    CouldNotConnectAgent,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::IllFormedNet => write!(
                f,
                "found a net that is not an active pair; this is not allowed in LaFont's syntax"
            ),
            Self::MissingSymbolDeclaration => write!(
                f,
                "found a net that has no matching symbol declaration in the program"
            ),
            Self::CouldNotConnectAgent => write!(f, "could not connect agent"),
        }
    }
}

impl error::Error for Error {}

pub fn compile(p: TypedProgram) -> Result<Program, Error> {
    let mut out: Vec<StackElem> = Default::default();

    let nets_by_active_pair = p
        .nets
        .iter()
        .filter_map(|net| match net {
            Net {
                lhs: Some(lhs),
                rhs: Some(rhs),
            } => Some(((lhs.name.0.as_str(), rhs.name.0.as_str()), (lhs, rhs))),
            _ => None,
        })
        .collect::<BTreeMap<(&str, &str), (&Agent, &Agent)>>();

    for net in &p.nets {
        let (lhs, rhs) = match net {
            Net {
                lhs: Some(lhs),
                rhs: Some(rhs),
            } => Ok((lhs, rhs)),
            _ => Err(Error::IllFormedNet),
        }?;

        // Nets fall into two categories:
        // - Human-reducible constants (i.e., they can be intuitively
        // reduced through their textual expression without any steps,
        // e.g., Z() >< Id(Z()). They are tautological, and are compiled
        // through strict copying
        //
        // TODO: In the future, optimize this to simply lazily copy
        // the input expression
        //
        // - Machine-reducible dynamic expressions (i.e, they require
        // steps to be reduced, and rely on intermediate reductions,
        // either literal, or themselves requiring reduction). Reduction
        // involves either: constant/literal copying, or substitution

        // Nets are literals if they do not mention
        // any nets which are members in an active pair in the program

        let requires_substitution = [lhs, rhs].iter().any(|redex_mem| {
            redex_mem
                .iter_child_agents()
                .filter(|agent| agent != &lhs && agent != &rhs)
                .any(|child| {
                    (|| {
                        let (lhs, rhs) = p.try_get_redex(child)?;

                        // The agent is not literal and requires substitution
                        // if there is an existing rule for the pair of
                        // agents
                        if nets_by_active_pair
                            .contains_key(&(lhs.name.0.as_str(), rhs.name.0.as_str()))
                        {
                            Some((lhs, rhs))
                        } else {
                            None
                        }
                    })()
                    .is_some()
                })
        });

        let (_agent_elems, agent_ptrs) = try_compile_nets(&mut out, &lhs, &rhs)?;

        let lhs_ptr = GlobalPtr::StackPtr(
            *agent_ptrs
                .get(&ptr::addr_of!(*lhs))
                .ok_or(Error::IllFormedNet)?,
        );

        if !requires_substitution {
            compile_literal(&mut out, lhs_ptr);

            continue;
        }
    }

    Ok(Program(out))
}

fn compile_literal(program: &mut Vec<StackElem>, lhs_ptr: GlobalPtr) {
    program.push(StackElem::Instr(Box::new(Op::PushRes(lhs_ptr))));
}

fn try_compile_nets(
    program: &mut Vec<StackElem>,
    lhs: &Agent,
    rhs: &Agent,
) -> Result<
    (
        BTreeMap<*const Agent, StackElem>,
        BTreeMap<*const Agent, Ptr>,
    ),
    Error,
> {
    let mut stack: Vec<StackElem> = Default::default();

    let start_ptr = program.len();

    let all_agents = || {
        lhs.iter_child_agents()
            .chain(rhs.iter_child_agents())
            .unique_by(|agent| ptr::addr_of!(**agent))
    };
    let all_symbols = || {
        all_agents()
            .map(|agent| agent.name.0.as_str())
            .unique()
            .enumerate()
            .map(|(fst, snd)| (snd, fst + start_ptr))
    };
    let all_symbols_pos = all_symbols().collect::<BTreeMap<_, _>>();

    stack.extend(
        all_symbols()
            .map(|(k, _)| k)
            .map(|key| StackElem::Ident((*key).to_owned())),
    );

    let (mut created_agent_elem, created_agent_pos): (
        BTreeMap<*const Agent, StackElem>,
        BTreeMap<*const Agent, Ptr>,
    ) = all_agents()
        .enumerate()
        .map(|(i, agent)| {
            let ident_ptr = all_symbols_pos.get(agent.name.0.as_str())?;

            let elem = StackElem::Agent(bc::Agent {
                name: GlobalPtr::StackPtr(*ident_ptr),
                ports: Default::default(),
            });

            Some((
                (ptr::addr_of!(*agent), elem),
                (ptr::addr_of!(*agent), i + start_ptr + all_symbols_pos.len()),
            ))
        })
        .collect::<Option<_>>()
        .ok_or(Error::MissingSymbolDeclaration)?;

    // Connect lhs and rhs agents
    created_agent_elem
        .get_mut(&ptr::addr_of!(*lhs))
        .and_then(|elem| elem.as_agent_mut())
        .ok_or(Error::CouldNotConnectAgent)?
        .push_port(GlobalPtr::StackPtr(
            *created_agent_pos
                .get(&ptr::addr_of!(*rhs))
                .ok_or(Error::CouldNotConnectAgent)?,
        ));
    created_agent_elem
        .get_mut(&ptr::addr_of!(*rhs))
        .and_then(|elem| elem.as_agent_mut())
        .ok_or(Error::CouldNotConnectAgent)?
        .push_port(GlobalPtr::StackPtr(
            *created_agent_pos
                .get(&ptr::addr_of!(*lhs))
                .ok_or(Error::CouldNotConnectAgent)?,
        ));

    // Connect agents
    all_agents()
        .map(|agent| {
            let agent_elem_ptr = created_agent_pos.get(&ptr::addr_of!(*agent))?;

            let new_ports = agent
                .ports
                .iter()
                .map(|port| match port {
                    Port::Agent(a) => {
                        let matching_stack_elem = created_agent_pos.get(&ptr::addr_of!(*a))?;

                        // Connect child to us as well in first position
                        created_agent_elem
                            .get_mut(&ptr::addr_of!(*a))
                            .and_then(|elem| elem.as_agent_mut())?
                            .push_port(GlobalPtr::StackPtr(*agent_elem_ptr));

                        Some(GlobalPtr::StackPtr(*matching_stack_elem))
                    }
                    Port::Var(v) => Some(GlobalPtr::StackPtr(*all_symbols_pos.get(v.0.as_str())?)),
                })
                .collect::<Option<Vec<_>>>()?;

            let agent_elem_mut = created_agent_elem
                .get_mut(&ptr::addr_of!(*agent))?
                .as_agent_mut()?;

            agent_elem_mut.ports.extend(new_ports);

            Some(())
        })
        .collect::<Option<()>>()
        .ok_or(Error::CouldNotConnectAgent)?;

    stack.extend(created_agent_elem.iter().map(|(_, x)| x.clone()));
    program.extend(stack);

    Ok((created_agent_elem, created_agent_pos))
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::{
        heuristics as heur,
        parser::parser_lafont::{lexer, parser},
    };
    use chumsky::Parser;

    #[test]
    fn test_compile_nets() {
        let cases = [(
            "type atom
             symbol Void: atom+
             symbol Id: atom-, atom+
             Void() >< Id(Void())",
            vec![
                StackElem::Ident("Void".to_owned()),
                StackElem::Ident("Id".to_owned()),
                StackElem::Agent(bc::Agent {
                    name: GlobalPtr::StackPtr(0),
                    ports: vec![GlobalPtr::StackPtr(3)],
                }),
                StackElem::Agent(bc::Agent {
                    name: GlobalPtr::StackPtr(1),
                    ports: vec![GlobalPtr::StackPtr(2), GlobalPtr::StackPtr(4)],
                }),
                StackElem::Agent(bc::Agent {
                    name: GlobalPtr::StackPtr(0),
                    ports: vec![GlobalPtr::StackPtr(3)],
                }),
                StackElem::Instr(Box::new(Op::PushRes(GlobalPtr::StackPtr(2)))),
            ],
        )];

        for (case, expected) in cases {
            let lexed = lexer()
                .parse(case)
                .unwrap()
                .into_iter()
                .flatten()
                .collect::<Vec<_>>();
            let parsed = parser().parse(lexed).unwrap();

            let (typed, _) = heur::parse_typed_program(parsed);

            let program = compile(typed).unwrap();
            assert_eq!(program, Program(expected));
        }
    }

    #[test]
    fn test_readback() {
        use super::super::vm;

        let cases = [(
            "type atom
             symbol Void: atom+
             symbol Id: atom-, atom+
             Void() >< Id(Void())",
            "Void() >< Id(Void())",
        )];

        for (case, expected) in cases {
            let lexed = lexer()
                .parse(case)
                .unwrap()
                .into_iter()
                .flatten()
                .collect::<Vec<_>>();
            let parsed = parser().parse(lexed).unwrap();

            let (typed, _) = heur::parse_typed_program(parsed);

            let program = compile(typed.clone()).unwrap();

            let mut results = vm::State::new(program, typed.symbol_declarations_for)
                .step_to_end()
                .unwrap();

            assert_eq!(results.remove(0).to_string(), expected);
        }
    }

    #[test_log::test]
    fn test_bruh() {
        use super::super::AgentPtr;

        let cases = [(
            "type atom
             symbol Void: atom+
             symbol Id: atom-, atom+
             Void() >< Id(Void())",
            vec![
                StackElem::Ident("Void".to_owned()),
                StackElem::Ident("Id".to_owned()),
                StackElem::Agent(bc::Agent {
                    name: GlobalPtr::StackPtr(0),
                    ports: vec![GlobalPtr::StackPtr(3)],
                }),
                StackElem::Agent(bc::Agent {
                    name: GlobalPtr::StackPtr(1),
                    ports: vec![GlobalPtr::StackPtr(2), GlobalPtr::StackPtr(4)],
                }),
                StackElem::Agent(bc::Agent {
                    name: GlobalPtr::StackPtr(0),
                    ports: vec![GlobalPtr::StackPtr(3)],
                }),
                StackElem::Instr(Box::new(Op::PushRes(GlobalPtr::StackPtr(2)))),
            ],
        )];

        for (case, expected) in cases {
            let lexed = lexer()
                .parse(case)
                .unwrap()
                .into_iter()
                .flatten()
                .collect::<Vec<_>>();
            let parsed = parser().parse(lexed).unwrap();

            let (typed, _) = heur::parse_typed_program(parsed);

            let mut program = compile(typed.clone()).unwrap();

            program.0.extend([
                StackElem::Ptr(GlobalPtr::AgentPtr(AgentPtr {
                    stack_pos: 3,
                    port: Some(0),
                })),
                StackElem::Ptr(GlobalPtr::StackPtr(6)).into(),
                Op::IncrPtrBy(1).into(),
                Op::Debug(GlobalPtr::StackPtr(6)).into(),
                Op::GoTo(6).into(),
            ]);

            let mut state = bc::vm::State::new(program, typed.symbol_declarations_for);
            state.step_to_end().unwrap();
        }
    }
}
