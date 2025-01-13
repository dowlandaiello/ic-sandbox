use super::{AgentPtr, GlobalPtr, Op, Program, Ptr, StackElem};
use crate::{
    bytecode2 as bc,
    heuristics::TypedProgram,
    parser::ast_lafont::{Agent, Net, Port, PortView},
};
use std::{
    backtrace::Backtrace,
    collections::{BTreeMap, BTreeSet},
    error, fmt,
    iter::Extend,
    ptr,
    rc::Rc,
};

#[derive(Debug)]
pub struct Error {
    trace: Backtrace,
    cause: ErrorCause,
}

impl From<ErrorCause> for Error {
    fn from(e: ErrorCause) -> Self {
        Self {
            trace: Backtrace::capture(),
            cause: e,
        }
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}:\n{}", self.cause, self.trace)
    }
}

#[derive(Copy, Clone, Debug)]
pub enum ErrorCause {
    /// Nets must all be active pairs in LaFont's syntax
    IllFormedNet,

    /// Programs must contain symbol declarations for all agents
    MissingSymbolDeclaration,

    CouldNotConnectAgent,
}

impl ErrorCause {
    fn into(self) -> Error {
        Error {
            cause: self,
            trace: Backtrace::capture(),
        }
    }
}

impl fmt::Display for ErrorCause {
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
    QueueRedex(Rc<NetRef<'a>>),
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

        let (all_ports, _) = lhs.iter_child_agents().chain(rhs.iter_child_agents()).fold(
            (Vec::new(), BTreeSet::new()),
            |(mut ports, mut seen): (Vec<PortView>, _), port| {
                if let PortView::Agent(a) = port {
                    if seen.contains(&ptr::addr_of!(*a)) {
                        return (ports, seen);
                    }

                    seen.insert(ptr::addr_of!(*a));
                }

                ports.push(port);

                (ports, seen)
            },
        );
        let all_symbols = all_ports
            .iter()
            .map(|port| match port {
                PortView::Agent(a) => a.name.0.as_str(),
                PortView::Var(v) => v.0.as_str(),
            })
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

        let (all_vars, all_vars_pos) = all_ports
            .iter()
            .filter_map(|port| match port {
                PortView::Var(v) => Some(v),
                _ => None,
            })
            .enumerate()
            .filter_map(|(i, v)| {
                let pos = all_symbols_pos.get(v.0.as_str())?;

                Some((
                    StackElem::Var(*pos),
                    (v.0.as_str(), i + start_ptr + prog.len()),
                ))
            })
            .collect::<(Vec<_>, BTreeMap<&str, Ptr>)>();

        prog.extend(all_vars);

        let all_agents = all_ports
            .iter()
            .filter_map(|port| match port {
                PortView::Agent(a) => Some(*a),
                _ => None,
            })
            .collect::<Vec<_>>();

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
                    (ptr::addr_of!(**agent), i + start_ptr + prog.len()),
                ))
            })
            .collect::<Option<_>>()
            .ok_or(ErrorCause::MissingSymbolDeclaration.into())?;

        // Connect lhs and rhs agents
        created_agent_elem
            .get_mut(&ptr::addr_of!(*lhs))
            .and_then(|elem| elem.as_agent_mut())
            .ok_or(ErrorCause::CouldNotConnectAgent.into())?
            .push_port(GlobalPtr::AgentPtr(AgentPtr {
                mem_pos: *created_agent_pos
                    .get(&ptr::addr_of!(*rhs))
                    .ok_or(ErrorCause::CouldNotConnectAgent.into())?,
                port: Some(0),
            }));
        created_agent_elem
            .get_mut(&ptr::addr_of!(*rhs))
            .and_then(|elem| elem.as_agent_mut())
            .ok_or(ErrorCause::CouldNotConnectAgent.into())?
            .push_port(GlobalPtr::AgentPtr(AgentPtr {
                mem_pos: *created_agent_pos
                    .get(&ptr::addr_of!(*lhs))
                    .ok_or(ErrorCause::CouldNotConnectAgent.into())?,
                port: Some(0),
            }));

        // Connect agents
        all_agents
            .iter()
            .map(|agent| {
                for port in agent.ports.iter() {
                    match port {
                        Port::Agent(a) => {
                            let src_elem_ptr = created_agent_pos.get(&ptr::addr_of!(**agent))?;
                            let dest_elem_ptr = created_agent_pos.get(&ptr::addr_of!(*a))?;

                            let n_ports_src = created_agent_elem
                                .get(&ptr::addr_of!(**agent))?
                                .as_agent()?
                                .ports
                                .len();
                            let n_ports_dest = created_agent_elem
                                .get(&ptr::addr_of!(*a))?
                                .as_agent()?
                                .ports
                                .len();

                            let src_elem_mut = created_agent_elem
                                .get_mut(&ptr::addr_of!(**agent))?
                                .as_agent_mut()?;

                            src_elem_mut.ports.push(GlobalPtr::AgentPtr(AgentPtr {
                                mem_pos: *dest_elem_ptr,
                                port: Some(n_ports_dest),
                            }));

                            let dest_elem_mut = created_agent_elem
                                .get_mut(&ptr::addr_of!(*a))?
                                .as_agent_mut()?;
                            dest_elem_mut.ports.push(GlobalPtr::AgentPtr(AgentPtr {
                                mem_pos: *src_elem_ptr,
                                port: Some(n_ports_src),
                            }));
                        }
                        Port::Var(v) => {
                            let src_elem_mut = created_agent_elem
                                .get_mut(&ptr::addr_of!(**agent))?
                                .as_agent_mut()?;

                            let var_ptr = GlobalPtr::MemPtr(*all_vars_pos.get(v.0.as_str())?);

                            src_elem_mut.ports.push(var_ptr);
                        }
                    }
                }

                Some(())
            })
            .collect::<Option<()>>()
            .ok_or(ErrorCause::CouldNotConnectAgent)?;

        prog.extend(
            all_agents
                .iter()
                .map(|a| created_agent_elem.remove(&ptr::addr_of!(**a)))
                .collect::<Option<Vec<_>>>()
                .ok_or(ErrorCause::IllFormedNet)?,
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
                BcBlock::QueueRedex(from) => {
                    let ptr = agent_ptrs.get(from.as_ref()).unwrap().clone();

                    src.extend([
                        Op::PushStack(StackElem::Ptr(GlobalPtr::MemPtr(ptr))).into(),
                        Op::QueueRedex.into(),
                    ]);
                }
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
                        src.extend([Op::PushMatchingRule.into()]);
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
                        Op::PushRedex.into(),
                        Op::Copy.into(),
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

    let all_net_pairs = p
        .nets
        .iter()
        .filter_map(|net| match net {
            Net {
                lhs: Some(lhs),
                rhs: Some(rhs),
            } => Some(((lhs.name.0.as_str(), rhs.name.0.as_str()), (lhs, rhs))),
            _ => None,
        })
        .collect::<Vec<_>>();

    // Get first occurrence of a rule with variables: this is a rule
    let (_, substituted) = all_net_pairs.into_iter().enumerate().fold(
        (BTreeSet::new(), Vec::new()),
        |(mut nets_by_pair, mut substituted), (i, ((lhs_name, rhs_name), (lhs, rhs)))| {
            let pair = (lhs_name, rhs_name);

            // Interactions with no variables are necessarily literals
            // and shall not be registered as rules
            if [lhs, rhs].iter().any(|redex_elem| {
                redex_elem
                    .iter_child_agents()
                    .filter(|view| matches!(view, PortView::Var(_)))
                    .count()
                    == 0
            }) {
                return (nets_by_pair, substituted);
            }

            if nets_by_pair.contains(&pair) {
                substituted.push(i);

                return (nets_by_pair, substituted);
            }

            nets_by_pair.insert(pair);

            (nets_by_pair, substituted)
        },
    );

    for (i, net) in p.nets.iter().enumerate() {
        let (lhs, rhs) = match net {
            Net {
                lhs: Some(lhs),
                rhs: Some(rhs),
            } => Ok((lhs, rhs)),
            _ => Err(ErrorCause::IllFormedNet.into()),
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

        let requires_substitution = substituted.contains(&i);

        let net_ref = Rc::new(NetRef::Intro { lhs, rhs });

        out.push(BcBlock::Referable(net_ref.clone()));

        if requires_substitution {
            let matching_rule_before_copy = Rc::new(NetRef::MatchingRule);
            let clone_net = Rc::new(NetRef::CloneNet(None));
            let cloned_sub_positions = Rc::new(NetRef::SubstitutionPositions {
                of_parent: None,
                of_child: None,
            });

            out.extend([BcBlock::QueueRedex(net_ref.clone())]);

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
        }

        out.push(BcBlock::PushRes(net_ref));
    }

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

    #[test_log::test]
    fn test_readback() {
        use super::super::vm;

        let cases = [(
            "type atom
             symbol Void: atom+
             symbol Id: atom-, atom+
             Void() >< Id(Void())",
            "Id(Void()) >< Void()",
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
    fn test_eval_literal() {
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

            let program = compile(typed.clone()).unwrap();

            let mut state = bc::vm::State::new(program, typed.symbol_declarations_for);
            state.step_to_end().unwrap();
        }
    }

    #[test_log::test]
    fn test_eval_substituted_easy() {
        let cases = [(
            "type nat
             symbol Z: nat+
             symbol Add: nat-, nat-, nat+
             Add(x, x) >< Z()
             Add(Z(), Z()) >< Z()",
            ["Z() >< Add(Z(), Z())", "Z() >< Add(Z(), Z())"],
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

            let mut state = bc::vm::State::new(program, typed.symbol_declarations_for);
            let mut res = state.step_to_end().unwrap();

            for expected_readback in expected {
                assert_eq!(res.remove(0).to_string().as_str(), expected_readback);
            }
        }
    }
}
