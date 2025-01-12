use super::{GlobalPtr, Op, Program, Ptr, StackElem};
use crate::{
    bytecode2 as bc,
    heuristics::TypedProgram,
    parser::ast_lafont::{Agent, Net, Port},
};
use std::{
    collections::{BTreeMap, BTreeSet},
    error, fmt,
    iter::Extend,
    ptr,
    rc::Rc,
};

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

#[derive(Ord, PartialOrd, Eq, PartialEq, Debug)]
pub enum BcBlock<'a> {
    Referable(Rc<NetRef<'a>>),
    Substitute,
    PushRes(Rc<NetRef<'a>>),
    IterRedex { stmts: Vec<BcBlock<'a>> },
}

#[derive(Ord, PartialOrd, Eq, PartialEq, Debug)]
pub enum NetRef<'a> {
    Intro {
        lhs: &'a Agent,
        rhs: &'a Agent,
    },
    MatchingRule,
    SubstitutionPositions {
        of_parent: Option<Rc<NetRef<'a>>>,
        of_child: Option<Rc<NetRef<'a>>>,
    },
    CloneNet(Option<Rc<NetRef<'a>>>),
}

#[derive(Debug, Default)]
pub struct Compiler<'a> {
    src: Program,
    agent_ptrs: BTreeMap<Rc<NetRef<'a>>, Ptr>,
}

impl<'a> Compiler<'a> {
    fn try_compile_net(
        start_ptr: Ptr,
        lhs: &Agent,
        rhs: &Agent,
    ) -> Result<
        (
            Vec<StackElem>,
            BTreeMap<*const Agent, StackElem>,
            BTreeMap<*const Agent, Ptr>,
        ),
        Error,
    > {
        let mut prog: Vec<StackElem> = Default::default();

        let (all_agents, _) = lhs.iter_child_agents().chain(rhs.iter_child_agents()).fold(
            (Vec::new(), BTreeSet::new()),
            |(mut agents, mut seen): (Vec<&Agent>, _), agent| {
                if seen.contains(&ptr::addr_of!(*agent)) {
                    return (agents, seen);
                }

                agents.push(agent);
                seen.insert(ptr::addr_of!(*agent));

                (agents, seen)
            },
        );
        let all_symbols = all_agents
            .iter()
            .map(|agent| agent.name.0.as_str())
            .collect::<BTreeSet<_>>()
            .into_iter()
            .enumerate()
            .map(|(fst, snd)| (snd, fst + start_ptr))
            .collect::<Vec<_>>();
        let all_symbols_pos = all_symbols.iter().cloned().collect::<BTreeMap<_, _>>();

        prog.extend(
            all_symbols
                .iter()
                .map(|(k, _)| k)
                .map(|key| StackElem::Ident((*key).to_owned())),
        );

        let (mut created_agent_elem, created_agent_pos): (
            BTreeMap<*const Agent, StackElem>,
            BTreeMap<*const Agent, Ptr>,
        ) = all_agents
            .iter()
            .enumerate()
            .map(|(i, agent)| {
                let ident_ptr = all_symbols_pos.get(agent.name.0.as_str())?;

                let elem = StackElem::Agent(bc::Agent {
                    name: GlobalPtr::MemPtr(*ident_ptr),
                    ports: Default::default(),
                });

                Some((
                    (ptr::addr_of!(**agent), elem),
                    (
                        ptr::addr_of!(**agent),
                        i + start_ptr + all_symbols_pos.len(),
                    ),
                ))
            })
            .collect::<Option<_>>()
            .ok_or(Error::MissingSymbolDeclaration)?;

        // Connect lhs and rhs agents
        created_agent_elem
            .get_mut(&ptr::addr_of!(*lhs))
            .and_then(|elem| elem.as_agent_mut())
            .ok_or(Error::CouldNotConnectAgent)?
            .push_port(GlobalPtr::MemPtr(
                *created_agent_pos
                    .get(&ptr::addr_of!(*rhs))
                    .ok_or(Error::CouldNotConnectAgent)?,
            ));
        created_agent_elem
            .get_mut(&ptr::addr_of!(*rhs))
            .and_then(|elem| elem.as_agent_mut())
            .ok_or(Error::CouldNotConnectAgent)?
            .push_port(GlobalPtr::MemPtr(
                *created_agent_pos
                    .get(&ptr::addr_of!(*lhs))
                    .ok_or(Error::CouldNotConnectAgent)?,
            ));

        // Connect agents
        all_agents
            .iter()
            .map(|agent| {
                let agent_elem_ptr = created_agent_pos.get(&ptr::addr_of!(**agent))?;

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
                                .push_port(GlobalPtr::MemPtr(*agent_elem_ptr));

                            Some(GlobalPtr::MemPtr(*matching_stack_elem))
                        }
                        Port::Var(v) => {
                            Some(GlobalPtr::MemPtr(*all_symbols_pos.get(v.0.as_str())?))
                        }
                    })
                    .collect::<Option<Vec<_>>>()?;

                let agent_elem_mut = created_agent_elem
                    .get_mut(&ptr::addr_of!(**agent))?
                    .as_agent_mut()?;

                agent_elem_mut.ports.extend(new_ports);

                Some(())
            })
            .collect::<Option<()>>()
            .ok_or(Error::CouldNotConnectAgent)?;

        prog.extend(
            all_agents
                .iter()
                .map(|a| created_agent_elem.remove(&ptr::addr_of!(**a)))
                .collect::<Option<Vec<_>>>()
                .ok_or(Error::IllFormedNet)?,
        );

        Ok((prog, created_agent_elem, created_agent_pos))
    }

    pub fn compile(&mut self, instrs: Vec<BcBlock<'a>>) -> Result<(), Error> {
        self.src = Program(Self::compile_section(0, &mut self.agent_ptrs, instrs)?);

        Ok(())
    }

    fn compile_section(
        start_ptr: Ptr,
        agent_ptrs: &mut BTreeMap<Rc<NetRef<'a>>, Ptr>,
        instrs: Vec<BcBlock<'a>>,
    ) -> Result<Vec<StackElem>, Error> {
        let mut src = Vec::new();

        for instr in instrs {
            match instr {
                BcBlock::Referable(r) => match r.clone().as_ref() {
                    NetRef::CloneNet(from) => {
                        if let Some(from) = from {
                            let ptr = agent_ptrs.get(from.as_ref()).unwrap().clone();

                            src.push(Op::PushStack(StackElem::Ptr(GlobalPtr::MemPtr(ptr))).into());
                        }

                        src.push(Op::CloneNet.into());
                    }
                    NetRef::Intro { lhs, rhs } => {
                        let (section, _, intro_agent_ptrs) =
                            Self::try_compile_net(start_ptr + src.len(), lhs, rhs)?;
                        src.extend(section);

                        agent_ptrs
                            .extend(intro_agent_ptrs.into_iter().map(|(_, v)| (r.clone(), v)));
                    }
                    NetRef::MatchingRule => {
                        src.push(Op::PushMatchingRule.into());
                    }
                    NetRef::SubstitutionPositions {
                        of_parent,
                        of_child,
                    } => {
                        if let Some(parent_instr) = of_parent {
                            let ptr = agent_ptrs.get(parent_instr.as_ref()).unwrap();
                            src.push(Op::PushStack(StackElem::Ptr(GlobalPtr::MemPtr(*ptr))).into());
                        }

                        if let Some(child_instr) = of_child {
                            let ptr = agent_ptrs.get(child_instr.as_ref()).unwrap();
                            src.push(Op::PushStack(StackElem::Ptr(GlobalPtr::MemPtr(*ptr))).into());
                        }

                        src.push(Op::PushSubstitutionPositions.into());
                    }
                },
                BcBlock::IterRedex { stmts } => {
                    let loop_start_ptr = start_ptr + src.len();

                    let compiled_instrs =
                        Self::compile_section(loop_start_ptr + 4, agent_ptrs, stmts)?;

                    src.extend([
                        Op::PopRedex.into(),
                        Op::PushStack(StackElem::None).into(),
                        Op::PushStack(StackElem::Ptr(GlobalPtr::MemPtr(
                            loop_start_ptr + 4 + compiled_instrs.len() + 2,
                        )))
                        .into(),
                        Op::GoToEq.into(),
                    ]);
                    src.extend(compiled_instrs);
                    src.extend([
                        Op::PushStack(StackElem::Ptr(GlobalPtr::MemPtr(loop_start_ptr))).into(),
                        Op::GoTo.into(),
                    ]);
                }
                BcBlock::PushRes(from) => {
                    let ptr = agent_ptrs.get(from.as_ref()).unwrap();

                    src.extend([
                        Op::PushStack(StackElem::Ptr(GlobalPtr::MemPtr(*ptr))).into(),
                        Op::PushRes.into(),
                    ]);
                }
                BcBlock::Substitute => {
                    src.push(Op::Substitute.into());
                }
            }
        }

        Ok(src)
    }
}

pub fn precompile<'a>(p: &'a TypedProgram) -> Result<Vec<BcBlock<'a>>, Error> {
    let mut out: Vec<BcBlock<'a>> = Default::default();

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

        let net_ref = Rc::new(NetRef::Intro { lhs, rhs });

        out.push(BcBlock::Referable(net_ref.clone()));

        if !requires_substitution {
            out.push(BcBlock::PushRes(net_ref));

            continue;
        }
    }

    let matching_rule_before_copy = Rc::new(NetRef::MatchingRule);
    let clone_net = Rc::new(NetRef::CloneNet(None));
    let cloned_sub_positions = Rc::new(NetRef::SubstitutionPositions {
        of_parent: None,
        of_child: None,
    });

    // While we have a redex left,
    out.push(BcBlock::IterRedex {
        stmts: vec![
            // The redex will be lhs port pointer, rhs port pointer
            // in stack [0], [-1]
            BcBlock::Referable(matching_rule_before_copy),
            BcBlock::Referable(clone_net),
            BcBlock::Referable(cloned_sub_positions.clone()),
            BcBlock::Substitute,
        ],
    });

    Ok(out)
}

pub fn compile(p: TypedProgram) -> Result<Program, Error> {
    let mut compiler = Compiler::default();
    compiler.compile(precompile(&p)?)?;

    Ok(compiler.src)
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
                StackElem::Ident("Id".to_owned()),
                StackElem::Ident("Void".to_owned()),
                StackElem::Agent(bc::Agent {
                    name: GlobalPtr::MemPtr(1),
                    ports: vec![GlobalPtr::MemPtr(3)],
                }),
                StackElem::Agent(bc::Agent {
                    name: GlobalPtr::MemPtr(0),
                    ports: vec![GlobalPtr::MemPtr(2), GlobalPtr::MemPtr(4)],
                }),
                StackElem::Agent(bc::Agent {
                    name: GlobalPtr::MemPtr(1),
                    ports: vec![GlobalPtr::MemPtr(3)],
                }),
                Op::PushStack(StackElem::Ptr(GlobalPtr::MemPtr(2))).into(),
                Op::PushRes.into(),
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
    fn test_loop() {
        use super::super::AgentPtr;

        let cases = ["type atom
             symbol Void: atom+
             symbol Id: atom-, atom+
             Void() >< Id(Void())"];

        for case in cases {
            let lexed = lexer()
                .parse(case)
                .unwrap()
                .into_iter()
                .flatten()
                .collect::<Vec<_>>();
            let parsed = parser().parse(lexed).unwrap();

            let (typed, _) = heur::parse_typed_program(parsed);

            let mut program = compile(typed.clone()).unwrap();

            tracing::debug!("{}", program);

            program.0.extend([
                Op::PushStack(StackElem::Ptr(GlobalPtr::AgentPtr(AgentPtr {
                    mem_pos: 3,
                    port: Some(0),
                })))
                .into(),
                Op::Copy.into(),
                Op::Debug.into(),
                Op::PushStack(StackElem::Offset(1)).into(),
                Op::IncrPtr.into(),
                Op::Copy.into(),
                Op::Deref.into(),
                Op::PushStack(StackElem::None).into(),
                Op::PushStack(StackElem::Ptr(GlobalPtr::MemPtr(8))).into(),
                Op::GoToNeq.into(),
            ]);

            tracing::debug!("{}", program);

            let mut state = bc::vm::State::new(program, typed.symbol_declarations_for);
            state.step_to_end().unwrap();
        }
    }

    #[test_log::test]
    fn identify_redex() {
        let cases = ["type atom
             symbol Void: atom+
             symbol Id: atom-, atom+
             Void() >< Id(Void())"];

        for case in cases {
            let lexed = lexer()
                .parse(case)
                .unwrap()
                .into_iter()
                .flatten()
                .collect::<Vec<_>>();
            let parsed = parser().parse(lexed).unwrap();

            let (typed, _) = heur::parse_typed_program(parsed);

            let mut program = compile(typed.clone()).unwrap();

            tracing::debug!("{}", program);

            tracing::debug!("{}", program);

            let mut state = bc::vm::State::new(program, typed.symbol_declarations_for);
            state.step_to_end().unwrap();
        }
    }
}
