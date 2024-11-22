use super::ast::{ActivePairMember, Expr, Instance, InstanceActivePair, Rule, VarName};
use std::{
    collections::{BTreeMap, BTreeSet, VecDeque},
    fmt, iter,
};

pub type AgentId = usize;

pub fn build_book_net(rules: Vec<Rule>) -> Vec<(Net, Net)> {
    rules
        .into_iter()
        .map(|rule| {
            let (mut net_lhs, mut net_rhs) = (Net::default(), Net::default());

            net_lhs.push_net(rule.lhs.lhs, rule.lhs.rhs);

            for member in rule.rhs {
                match member {
                    Instance::ActivePair(member) => {
                        net_rhs.push_net(member.lhs, member.rhs);
                    }
                    Instance::PairMember(ActivePairMember::Agent {
                        name,
                        inactive_vars: _,
                    }) => {
                        net_rhs.push_ast_agent(name);
                    }
                    Instance::PairMember(ActivePairMember::Var(v)) => {
                        net_rhs.push_name(v);
                    }
                }
            }

            (net_lhs, net_rhs)
        })
        .collect::<Vec<_>>()
}

pub fn build_instance_net(instance: Vec<Instance>) -> Option<Net> {
    let mut n = Net::default();

    for member in instance {
        match member {
            Instance::ActivePair(member) => {
                n.push_net(member.lhs, member.rhs);
            }
            Instance::PairMember(ActivePairMember::Agent {
                name,
                inactive_vars: _,
            }) => {
                n.push_ast_agent(name);
            }
            Instance::PairMember(ActivePairMember::Var(v)) => {
                n.push_name(v);
            }
        }
    }

    Some(n)
}

pub fn build_application_net(
    rules: Vec<Rule>,
    instance: Vec<Instance>,
) -> Option<(Vec<(Net, Net)>, Net)> {
    // Gather all nets representing rules
    let nets = build_book_net(rules);

    let n = build_instance_net(instance)?;

    Some((nets, n))
}

pub fn reduce_expr_to_end_or_infinity(e: Expr) -> Vec<Instance> {
    match e
        .to_application()
        .and_then(|(rules, instance)| build_application_net(rules, instance))
    {
        Some((rules, instance)) => reduce_to_end_or_infinity(&rules, instance),
        _ => Vec::new(),
    }
}

/// Reduces an expression to completion in the context of some rule.
pub fn reduce_to_end_or_infinity(nets: &[(Net, Net)], instance_net: Net) -> Vec<Instance> {
    let mut results = Vec::new();
    let mut to_reduce = vec![instance_net];

    while let Some(curr_redex) = to_reduce.pop() {
        let new = if let Some(result) = reduce_net(nets, curr_redex.clone()) {
            result
        } else {
            break;
        };

        if new == curr_redex {
            tracing::trace!("reached end of reduction: same expr");

            results.push(new);

            break;
        };

        if new
            .active_pairs
            .iter()
            .filter(|(a, b)| matches!((a, b), (&PairElem::Agent(_), &PairElem::Agent(_))))
            .count()
            > 0
        {
            to_reduce.push(new);
        } else {
            tracing::trace!("reached end of reduction: no active pairs");

            results.push(new);
        }
    }

    results
        .into_iter()
        .map(|n| <Net as Into<Vec<Instance>>>::into(n))
        .flatten()
        .collect::<Vec<_>>()
}

pub fn reduce_once(nets: Vec<(Net, Net)>, instance_net: Net) -> Option<Vec<Instance>> {
    reduce_net(nets.as_slice(), instance_net).map(|n| <Net as Into<Vec<Instance>>>::into(n))
}

fn matching_nets<'a>(
    rules_nets: &'a [(Net, Net)],
    instance: &'a Net,
    redex_lhs: PairElem,
    redex_rhs: PairElem,
) -> Vec<(&'a Net, &'a Net)> {
    rules_nets
        .iter()
        .filter_map(|(lhs, rhs)| {
            let (agent_a, agent_b) = lhs.active_pairs.iter().next()?;

            let pair_a: BTreeSet<&str> =
                BTreeSet::from_iter(vec![lhs.get_name_for(agent_a), lhs.get_name_for(agent_b)]);
            let pair_b = BTreeSet::from_iter(vec![
                instance.get_name_for(&redex_lhs),
                instance.get_name_for(&redex_rhs),
            ]);

            if pair_a == pair_b
                || pair_a.is_subset(&pair_b)
                || (agent_a.is_var() && agent_b.is_var())
                || ((agent_a.is_var() ^ agent_b.is_var())
                    && pair_b.intersection(&pair_a).count() > 0)
            {
                return Some((lhs, rhs));
            }

            None
        })
        .collect::<Vec<_>>()
}

// Replace vars and unwritten ports in rhs with nets in instance matching vars
#[derive(Debug)]
enum ReplacementTarget {
    AgentPort { agent_idx: usize, port: usize },
    WholeVar { var_idx: usize },
    WholeAgent { agent_idx: usize },
}

#[derive(Debug)]
enum ReplacementOp {
    Replace(ReplacementTarget),
    Copy(ReplacementTarget),
}

fn reduce_net(rules_nets: &[(Net, Net)], mut instance: Net) -> Option<Net> {
    fn fmt_pair_elem(net: &Net, pair_elem: &PairElem) -> String {
        match pair_elem {
            PairElem::Var(v) => net.names[*v].clone(),
            PairElem::Agent(idx) => net.names[net.agents[*idx].id].clone(),
        }
    }

    fn fmt_replacement_target(net: &Net, target: &ReplacementTarget) -> String {
        match target {
            ReplacementTarget::WholeAgent { agent_idx } => {
                net.names[net.agents[*agent_idx].id].clone()
            }
            ReplacementTarget::WholeVar { var_idx } => net.names[*var_idx].clone(),
            ReplacementTarget::AgentPort { agent_idx, port } => format!(
                "{}[{} @ {}, ..]",
                net.names[net.agents[*agent_idx].id],
                match net.agents[*agent_idx].ports[*port] {
                    PairElem::Agent(agent_idx) => fmt_replacement_target(
                        net,
                        &ReplacementTarget::WholeAgent {
                            agent_idx: agent_idx
                        }
                    ),
                    PairElem::Var(var_idx) => fmt_replacement_target(
                        net,
                        &ReplacementTarget::WholeVar { var_idx: var_idx }
                    ),
                },
                port
            ),
        }
    }

    fn fmt_replacement_op(net: &Net, op: &ReplacementOp) -> String {
        match op {
            ReplacementOp::Copy(c) => format!("Copy({})", fmt_replacement_target(net, c)),
            ReplacementOp::Replace(r) => format!("Replace({})", fmt_replacement_target(net, r)),
        }
    }

    // TODO: Consider building an entirely new net instead of doing it in place

    // Pushes a new AST agent
    fn push_elem_recursively(
        to_insert_conns: &mut BTreeSet<(PairElem, PairElem)>,
        replaced: &mut BTreeMap<PairElem, PairElem>,
        original: &Net,
        original_elem: &PairElem,
        n: &mut Net,
    ) -> usize {
        let (idx, mut to_insert) = match original_elem {
            PairElem::Agent(original_idx) => {
                tracing::debug!(
                    "inserting agent {}",
                    original.names[original.agents[*original_idx].id]
                );

                let idx =
                    n.push_ast_agent(original.names[original.agents[*original_idx].id].clone());

                (
                    idx,
                    VecDeque::from_iter(
                        original.agents[*original_idx]
                            .ports
                            .iter()
                            .skip(1)
                            .enumerate()
                            .map(|(a, x)| (idx, a, x)),
                    ),
                )
            }
            PairElem::Var(idx) => {
                tracing::debug!("inserting var {}", original.names[*idx]);

                (n.push_name(original.names[*idx].clone()), VecDeque::new())
            }
        };

        // TODO: Might have to do something with replacements in here?
        while let Some((agent_connect_idx, port, insertion_elem)) = to_insert.pop_front() {
            match insertion_elem {
                PairElem::Agent(a) => {
                    tracing::trace!("{:?} {:?} {:?}", agent_connect_idx, n.agents, n.names,);
                    tracing::debug!(
                        "recursively inserting agent {} in port {} of agent {}",
                        original.names[original.agents[*a].id],
                        port,
                        n.names[n.agents[agent_connect_idx].id],
                    );

                    let idx = n.push_ast_agent(original.names[original.agents[*a].id].clone());

                    replaced.insert(PairElem::Agent(*a), PairElem::Agent(idx));

                    to_insert_conns
                        .insert((PairElem::Agent(agent_connect_idx), PairElem::Agent(idx)));

                    to_insert.extend(
                        original.agents[*a]
                            .ports
                            .iter()
                            .enumerate()
                            .skip(1)
                            .map(|(i, x)| (idx, i, x))
                            .collect::<Vec<_>>(),
                    );
                }
                PairElem::Var(v) => {
                    tracing::debug!(
                        "inserting var {} in port {} of agent {}",
                        original.names[*v],
                        port,
                        n.names[n.agents[agent_connect_idx].id],
                    );

                    let name = original.names[*v].clone();

                    let idx = n.push_name(name);

                    replaced.insert(PairElem::Var(*v), PairElem::Var(idx));

                    to_insert_conns
                        .insert((PairElem::Agent(agent_connect_idx), PairElem::Var(idx)));
                }
            }
        }

        idx
    }

    tracing::debug!(
        "reducing net {} with next active pairs {}",
        instance,
        instance
            .active_pairs
            .iter()
            .map(|(a, b)| format!(
                "{} >< {}",
                fmt_pair_elem(&instance, &a),
                fmt_pair_elem(&instance, &b)
            ))
            .collect::<Vec<String>>()
            .join(", ")
    );

    let (redex_lhs, redex_rhs) = instance.active_pairs.pop_first()?;

    tracing::debug!("reducing active pair {:?} ~ {:?}", redex_lhs, redex_rhs);

    let (matching_rule, matching_replacement_ref) =
        matching_nets(rules_nets, &instance, redex_lhs.clone(), redex_rhs.clone()).remove(0);
    let matching_replacement = matching_replacement_ref.clone();
    let mut matching_replacement_buffer = Net::default();

    tracing::debug!("matching rule candidate: {}", matching_rule);
    tracing::debug!(
        "matching replacement candidate: {} with active pairs {}",
        matching_replacement,
        matching_replacement
            .active_pairs
            .iter()
            .map(|(a, b)| format!(
                "{} >< {}",
                fmt_pair_elem(&matching_replacement, &a),
                fmt_pair_elem(&matching_replacement, &b)
            ))
            .collect::<Vec<String>>()
            .join(", ")
    );

    // Replacement candidates are just all variables
    // variables are either:
    // - Whole variables (as in not connected)
    // - terminal variables (no auxilary ports)
    let to_replace = matching_replacement
        .active_pairs
        .iter()
        .map(|(a, b)| {
            [a.clone(), b.clone()]
                .into_iter()
                .map(|redex| match redex {
                    PairElem::Var(v) => {
                        ReplacementOp::Replace(ReplacementTarget::WholeVar { var_idx: v })
                    }
                    PairElem::Agent(a) => {
                        ReplacementOp::Copy(ReplacementTarget::WholeAgent { agent_idx: a })
                    }
                })
                .chain(
                    matching_replacement
                        .agents
                        .iter()
                        .enumerate()
                        .map(|(a, agent)| {
                            agent
                                .ports
                                .iter()
                                .enumerate()
                                .skip(1)
                                .map(|(i, port_elem)| match port_elem {
                                    PairElem::Agent(a) => {
                                        if matching_replacement.agents[*a].ports.len() == 1 {
                                            ReplacementOp::Replace(ReplacementTarget::AgentPort {
                                                agent_idx: *a,
                                                port: i,
                                            })
                                        } else {
                                            ReplacementOp::Copy(ReplacementTarget::WholeAgent {
                                                agent_idx: *a,
                                            })
                                        }
                                    }
                                    PairElem::Var(_) => {
                                        ReplacementOp::Replace(ReplacementTarget::AgentPort {
                                            agent_idx: a,
                                            port: i,
                                        })
                                    }
                                })
                                .collect::<Vec<_>>()
                        })
                        .flatten(),
                )
        })
        .flatten()
        .collect::<Vec<_>>();

    // Map of each replacement target to which node it is connected to
    let to_replace_conns = matching_replacement
        .active_pairs
        .iter()
        .cloned()
        .chain(
            matching_replacement
                .agents
                .iter()
                .enumerate()
                .map(|(i, agent)| {
                    agent
                        .ports
                        .iter()
                        .map(|conn| (PairElem::Agent(i), conn.clone()))
                        .collect::<Vec<_>>()
                })
                .flatten(),
        )
        .collect::<BTreeSet<(PairElem, PairElem)>>();
    let mut to_insert_conns: BTreeSet<(PairElem, PairElem)> = Default::default();

    // Mapping from old indexes to new indexes
    let mut replaced: BTreeMap<PairElem, PairElem> = BTreeMap::default();

    // Replacement candidates are clockwise terminal elements--as in they have
    // no "children"--as in they only have one connection
    // nodes cannot be fully disjoint
    // - This handles x ~ y identity case
    //   - Neither x nor y have aux ports
    // - This handles A ~ x 1/2 identity case
    //   - Neither A, nor x have aux ports
    // - This handles the general case A[x, y] ~ B[z]
    //   - Neither x, y, or z have aux ports
    // Replacement candidates without aux ports can be identified in the rhs
    // net by iterating over candidates, where candidates is defined
    // as the set of variables and agents in the net
    // and checking if they have no aux ports, or are a variable
    // all variables are necessarily candidates
    let replacement_candidates = iter::once(redex_lhs.clone())
        .chain(
            [redex_lhs.clone(), redex_rhs.clone()]
                .into_iter()
                .map(|redex| match redex {
                    PairElem::Agent(a) => instance.agents[a]
                        .ports
                        .iter()
                        .skip(1)
                        .enumerate()
                        .map(|(_, port_elem)| port_elem.clone())
                        .collect::<Vec<_>>(),
                    PairElem::Var(_) => vec![],
                })
                .flatten(),
        )
        .chain(iter::once(redex_rhs.clone()));
    let n_replacement_candidates = replacement_candidates.clone().count();

    let redexes = BTreeSet::from_iter([redex_lhs.clone(), redex_rhs.clone()]);

    // Candidates must be replaced if:
    // - They are a variable
    // - They are connected to a redex
    let mut replacements_unordered = replacement_candidates
        .enumerate()
        .filter(|(_, elem)| {
            (!redexes.contains(&elem) || n_replacement_candidates == 2)
                || match elem {
                    PairElem::Var(_) => true,
                    PairElem::Agent(a) => instance.agents[*a].ports.len() == 1,
                }
        })
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect::<Vec<_>>();
    replacements_unordered.sort_by_key(|(i, _)| *i);

    let mut replacements = replacements_unordered
        .into_iter()
        .map(|(_, x)| x)
        .collect::<Vec<_>>();

    tracing::debug!(
        "replacing (agents, ports) {} with {} in net {} {:?}",
        to_replace
            .iter()
            .map(|target| fmt_replacement_op(&matching_replacement, &target))
            .collect::<Vec<String>>()
            .join(", "),
        replacements
            .iter()
            .map(|target| fmt_pair_elem(&instance, &target))
            .collect::<Vec<String>>()
            .join(", "),
        matching_replacement,
        matching_replacement
    );

    // Algorithm for auxiliary insertion of replaced nodes:
    // - We can already insert replaced ndoes and all their children
    // - How do we insert parent nodes?
    // - Just insert parent nodes as normally, and look for replacement
    // nodes for insertoin candidates

    for replacement_op in to_replace {
        tracing::debug!(
            "visiting {}",
            fmt_replacement_op(&matching_replacement, &replacement_op),
        );

        match replacement_op {
            ReplacementOp::Copy(replacement_target) => match replacement_target {
                ReplacementTarget::WholeVar { var_idx } => {
                    let idx = matching_replacement_buffer
                        .push_name(matching_replacement.names[var_idx].clone());

                    replaced.insert(PairElem::Var(var_idx), PairElem::Var(idx));
                }
                ReplacementTarget::WholeAgent { agent_idx } => {
                    let idx = matching_replacement_buffer.push_ast_agent(
                        matching_replacement.names[matching_replacement.agents[agent_idx].id]
                            .clone(),
                    );

                    replaced.insert(PairElem::Agent(agent_idx), PairElem::Agent(idx));
                }
                ReplacementTarget::AgentPort { .. } => {}
            },
            ReplacementOp::Replace(replacement_target) => {
                let replacement_elem = replacements.remove(0);

                match replacement_target {
                    ReplacementTarget::AgentPort { agent_idx, port } => {
                        // Insert the actual agent
                        match replacement_elem {
                            p @ PairElem::Agent(_) => {
                                tracing::trace!("pushing AgentPort -> Agent");

                                let idx = push_elem_recursively(
                                    &mut to_insert_conns,
                                    &mut replaced,
                                    &instance,
                                    &p,
                                    &mut matching_replacement_buffer,
                                );

                                replaced.insert(
                                    matching_replacement.agents[agent_idx].ports[port].clone(),
                                    PairElem::Agent(idx),
                                );

                                tracing::trace!(
                                    "connecting {} -> {}",
                                    fmt_pair_elem(
                                        &matching_replacement,
                                        &PairElem::Agent(agent_idx)
                                    ),
                                    fmt_pair_elem(
                                        &matching_replacement_buffer,
                                        &PairElem::Agent(idx)
                                    )
                                );

                                /*matching_replacement_buffer
                                .connect(replaced[&PairElem::Agent(agent_idx)].get_idx(), idx);*/

                                tracing::debug!(
                                    "made replacement AgentPort {} -> Agent {}: {:?}",
                                    fmt_pair_elem(
                                        &matching_replacement,
                                        &matching_replacement.agents[agent_idx].ports[port].clone()
                                    ),
                                    fmt_pair_elem(
                                        &matching_replacement_buffer,
                                        &PairElem::Agent(idx)
                                    ),
                                    matching_replacement_buffer
                                );

                                idx
                            }
                            PairElem::Var(v) => {
                                tracing::trace!("pushing AgentPort -> Var");

                                let idx = matching_replacement_buffer
                                    .push_name(instance.names[v].clone());

                                replaced.insert(
                                    matching_replacement.agents[agent_idx].ports[port].clone(),
                                    PairElem::Var(idx),
                                );

                                tracing::debug!(
                                    "made replacement AgentPort {} -> Var {}: {:?}",
                                    fmt_pair_elem(
                                        &matching_replacement,
                                        &matching_replacement.agents[agent_idx].ports[port].clone()
                                    ),
                                    fmt_pair_elem(
                                        &matching_replacement_buffer,
                                        &PairElem::Var(idx)
                                    ),
                                    matching_replacement_buffer,
                                );

                                idx
                            }
                        };

                        // Connect all connected agents
                    }
                    ReplacementTarget::WholeVar { var_idx } => {
                        // We will always have to push a new agent
                        match replacement_elem {
                            p @ PairElem::Agent(_) => {
                                tracing::trace!("pushing WholeVar -> Agent");

                                // Connect any connected nodes, if they exist (look for connections to this var idx)
                                let idx = push_elem_recursively(
                                    &mut to_insert_conns,
                                    &mut replaced,
                                    &instance,
                                    &p,
                                    &mut matching_replacement_buffer,
                                );

                                replaced.insert(PairElem::Var(var_idx), PairElem::Agent(idx));

                                tracing::debug!(
                                    "made replacement WholeVar {} -> Agent {}: {:?}",
                                    fmt_pair_elem(&matching_replacement, &PairElem::Var(var_idx),),
                                    fmt_pair_elem(
                                        &matching_replacement_buffer,
                                        &PairElem::Agent(idx)
                                    ),
                                    matching_replacement_buffer
                                );
                            }
                            PairElem::Var(v) => {
                                tracing::trace!("pushing WholeVar -> Var");

                                // Map indexes of connected nodes onto new indexes
                                // to enable active pair replacement

                                let idx = matching_replacement_buffer
                                    .push_name(instance.names[v].clone());

                                replaced.insert(PairElem::Var(var_idx), PairElem::Var(idx));

                                tracing::debug!(
                                    "made replacement WholeVar {} -> Var {}: {:?}",
                                    fmt_pair_elem(&matching_replacement, &PairElem::Var(var_idx),),
                                    fmt_pair_elem(
                                        &matching_replacement_buffer,
                                        &PairElem::Var(idx)
                                    ),
                                    matching_replacement_buffer
                                );
                            }
                        };
                    }
                    ReplacementTarget::WholeAgent { agent_idx } => {
                        match replacement_elem {
                            p @ PairElem::Agent(_) => {
                                tracing::trace!("pushing WholeAgent -> Agent");

                                // Connect any connected nodes, if they exist (look for connections to this var idx)
                                let idx = push_elem_recursively(
                                    &mut to_insert_conns,
                                    &mut replaced,
                                    &instance,
                                    &p,
                                    &mut matching_replacement_buffer,
                                );

                                replaced.insert(PairElem::Agent(agent_idx), PairElem::Agent(idx));

                                tracing::debug!(
                                    "made replacement WholeAgent {} -> Agent {}: {:?}",
                                    fmt_pair_elem(
                                        &matching_replacement,
                                        &PairElem::Agent(agent_idx)
                                    ),
                                    fmt_pair_elem(
                                        &matching_replacement_buffer,
                                        &PairElem::Agent(idx)
                                    ),
                                    matching_replacement_buffer
                                );
                            }
                            PairElem::Var(v) => {
                                tracing::trace!("pushing WholeAgent -> Var");

                                // Map indexes of connected nodes onto new indexes
                                // to enable active pair replacement

                                let idx = matching_replacement_buffer
                                    .push_name(instance.names[v].clone());

                                replaced.insert(PairElem::Agent(agent_idx), PairElem::Var(idx));

                                tracing::debug!(
                                    "made replacement WholeAgent {} -> Var {}: {:?}",
                                    fmt_pair_elem(
                                        &matching_replacement,
                                        &PairElem::Agent(agent_idx)
                                    ),
                                    fmt_pair_elem(
                                        &matching_replacement_buffer,
                                        &PairElem::Var(idx)
                                    ),
                                    matching_replacement_buffer
                                );
                            }
                        }
                    }
                }
            }
        }
    }

    // Rewire all old connections using new nodes
    tracing::debug!(
        "looking for active pairs {}",
        to_replace_conns
            .iter()
            .map(|(redex_lhs, redex_rhs)| format!(
                "{} >< {}",
                fmt_pair_elem(&matching_replacement, &redex_lhs),
                fmt_pair_elem(&matching_replacement, &redex_rhs)
            ))
            .collect::<Vec<String>>()
            .join(", ")
    );

    tracing::debug!("reduction resulted in replacements: {:?}", replaced);

    tracing::debug!("need to wire: {:?}", to_insert_conns);

    for (active_pair_elem_a, active_pair_elem_b) in to_replace_conns.into_iter() {
        let replaced = (
            replaced[&active_pair_elem_a].clone(),
            replaced[&active_pair_elem_b].clone(),
        );

        tracing::debug!(
            "visiting replaced active pair: {} >< {} -> {} >< {}",
            fmt_pair_elem(&matching_replacement, &active_pair_elem_a),
            fmt_pair_elem(&matching_replacement, &active_pair_elem_b),
            fmt_pair_elem(&matching_replacement_buffer, &replaced.0),
            fmt_pair_elem(&matching_replacement_buffer, &replaced.1)
        );

        match replaced {
            (PairElem::Agent(a), PairElem::Agent(b)) => {
                matching_replacement_buffer.connect(a, b);
            }
            (PairElem::Agent(a), PairElem::Var(b)) => {
                matching_replacement_buffer
                    .push_var(a, matching_replacement_buffer.names[b].clone());
            }
            (PairElem::Var(a), PairElem::Agent(b)) => {
                matching_replacement_buffer
                    .push_var(b, matching_replacement_buffer.names[a].clone());
            }
            (PairElem::Var(a), PairElem::Var(b)) => {
                tracing::debug!(
                    "found active pair: {} >< {}",
                    fmt_pair_elem(&matching_replacement_buffer, &PairElem::Var(a)),
                    fmt_pair_elem(&matching_replacement_buffer, &PairElem::Var(b))
                );

                matching_replacement_buffer
                    .active_pairs
                    .insert((PairElem::Var(a), PairElem::Var(b)));
            }
        };
    }

    for (pair_elem_a, pair_elem_b) in to_insert_conns.into_iter() {
        tracing::debug!(
            "visiting inserted pair: {} ~ {}",
            fmt_pair_elem(&matching_replacement_buffer, &pair_elem_a),
            fmt_pair_elem(&matching_replacement_buffer, &pair_elem_b),
        );

        match (pair_elem_a, pair_elem_b) {
            (PairElem::Agent(a), PairElem::Agent(b)) => {
                matching_replacement_buffer.connect(a, b);
            }
            (PairElem::Agent(a), PairElem::Var(b)) => {
                matching_replacement_buffer
                    .push_var(a, matching_replacement_buffer.names[b].clone());
            }
            (PairElem::Var(a), PairElem::Agent(b)) => {
                matching_replacement_buffer
                    .push_var(b, matching_replacement_buffer.names[a].clone());
            }
            (PairElem::Var(_), PairElem::Var(_)) => {}
        };
    }

    fn order_pair(active_pair: (PairElem, PairElem)) -> (PairElem, PairElem) {
        if active_pair.0 < active_pair.1 {
            active_pair
        } else {
            (active_pair.1, active_pair.0)
        }
    }

    // Connect all agents that have shared ports
    matching_replacement_buffer.active_pairs.extend(
        matching_replacement_buffer
            .agents
            .iter()
            .enumerate()
            .filter_map(|(i, agent)| match &agent.ports[0] {
                PairElem::Agent(agent_idx) => {
                    (matching_replacement_buffer.agents[*agent_idx].ports[0] == PairElem::Agent(i))
                        .then(|| order_pair((PairElem::Agent(i), PairElem::Agent(*agent_idx))))
                }
                v @ PairElem::Var(_) => Some(order_pair((PairElem::Agent(i), v.clone()))),
            }),
    );

    tracing::debug!(
        "reduction resulted in {} {:?}",
        matching_replacement_buffer,
        matching_replacement_buffer
    );

    Some(matching_replacement_buffer)
}

#[derive(Debug, Default, Clone, PartialEq)]
pub struct Net {
    names: Vec<VarName>,
    agents: Vec<Box<Agent>>,
    active_pairs: BTreeSet<(PairElem, PairElem)>,
}

#[derive(Hash, Debug, PartialEq, Eq, Clone, Ord, PartialOrd)]
pub enum PairElem {
    Var(usize),
    Agent(usize),
}

impl PairElem {
    pub fn is_var(&self) -> bool {
        matches!(self, Self::Var(_))
    }

    pub fn is_agent(&self) -> bool {
        matches!(self, Self::Agent(_))
    }

    pub fn get_idx(&self) -> usize {
        match self {
            Self::Var(i) => *i,
            Self::Agent(i) => *i,
        }
    }
}

impl fmt::Display for Net {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let pairs: Vec<Instance> = self.clone().into();

        write!(
            f,
            "{}",
            pairs
                .iter()
                .map(|p| p.to_string())
                .collect::<Vec<_>>()
                .join(", ")
        )
    }
}

impl From<Net> for Vec<Instance> {
    fn from(n: Net) -> Self {
        n.active_pairs
            .iter()
            .map(|(redex_lhs, redex_rhs)| {
                Instance::ActivePair(InstanceActivePair {
                    lhs: match redex_lhs {
                        PairElem::Var(v) => ActivePairMember::Var(n.names[*v].clone()),
                        PairElem::Agent(a) => n.agent_to_pair_member(*a, Default::default()),
                    },
                    rhs: match redex_rhs {
                        PairElem::Var(v) => ActivePairMember::Var(n.names[*v].clone()),
                        PairElem::Agent(a) => n.agent_to_pair_member(*a, Default::default()),
                    },
                })
            })
            .collect::<Vec<_>>()
    }
}

impl Net {
    pub fn get_name_for(&self, elem: &PairElem) -> &str {
        match elem {
            PairElem::Var(v) => self.names[*v].as_str(),
            PairElem::Agent(a) => self.names[self.agents[*a].id].as_str(),
        }
    }

    pub fn agent_to_pair_member(
        &self,
        agent_idx: usize,
        mut visited: BTreeSet<usize>,
    ) -> ActivePairMember {
        let a = &self.agents[agent_idx];

        ActivePairMember::Agent {
            name: self.names[a.id].clone(),
            inactive_vars: a
                .ports
                .iter()
                .skip(1)
                .filter(|p| match p {
                    PairElem::Var(_) => true,
                    PairElem::Agent(p) => {
                        let v = !visited.contains(&p);
                        visited.insert(*p);

                        v
                    }
                })
                .collect::<Vec<_>>()
                .into_iter()
                .map(|maybe_p| match maybe_p {
                    PairElem::Var(v) => ActivePairMember::Var(self.names[*v].clone()),
                    PairElem::Agent(port) => self.agent_to_pair_member(*port, visited.clone()),
                })
                .collect::<Vec<_>>(),
        }
    }

    pub fn get_port(&self, node_a_idx: usize, port_idx: usize) -> &PairElem {
        &self.agents[node_a_idx].ports[port_idx]
    }

    pub fn push_name(&mut self, name: VarName) -> usize {
        self.names
            .iter()
            .position(|maybe_name| *maybe_name == *name)
            .unwrap_or_else(|| {
                self.names.push(name);
                self.names.len() - 1
            })
    }

    #[tracing::instrument]
    pub fn push_net(&mut self, lhs: ActivePairMember, rhs: ActivePairMember) {
        // Push and connect lhs and rhs
        let (lhs_loc, rhs_loc) = self.push_redex(lhs.clone(), rhs.clone());

        // Connect all aux ports to lhs and rhs
        // Note: these vars are necessarily inactive, no need to skip first
        let mut to_insert = lhs_loc
            .map(|loc| {
                lhs.get_inactive_vars()
                    .unwrap_or_default()
                    .iter()
                    .enumerate()
                    .map(|(i, member)| (loc, 1 + i, member))
                    .collect::<VecDeque<_>>()
            })
            .unwrap_or_default();

        // Same here
        if let Some(loc) = rhs_loc {
            to_insert.extend(
                rhs.get_inactive_vars()
                    .unwrap_or_default()
                    .iter()
                    .enumerate()
                    .map(|(i, member)| (loc, 1 + i, member))
                    .collect::<VecDeque<_>>(),
            );
        }

        while let Some((conn_agent_idx, _, expr_insert)) = to_insert.pop_front() {
            match expr_insert {
                ActivePairMember::Agent {
                    name,
                    inactive_vars,
                } => {
                    let id = self.push_ast_agent(name.clone());
                    self.connect(id, conn_agent_idx);

                    // Continue with the child's inactive vars
                    to_insert.extend(
                        inactive_vars
                            .iter()
                            .enumerate()
                            .map(|(i, member)| (id, 1 + i, member))
                            .collect::<VecDeque<_>>(),
                    );
                }
                ActivePairMember::Var(v) => {
                    self.push_var(conn_agent_idx, v.clone());
                }
            }
        }
    }

    #[tracing::instrument]
    pub fn push_redex(
        &mut self,
        lhs: ActivePairMember,
        rhs: ActivePairMember,
    ) -> (Option<usize>, Option<usize>) {
        match (lhs, rhs) {
            // Redex between agents
            (
                ActivePairMember::Agent {
                    name: name_lhs,
                    inactive_vars: _,
                },
                ActivePairMember::Agent {
                    name: name_rhs,
                    inactive_vars: _,
                },
            ) => {
                let idx_agent_a = self.push_ast_agent(name_lhs);
                let idx_agent_b = self.push_ast_agent(name_rhs);

                self.connect(idx_agent_a, idx_agent_b);

                self.active_pairs
                    .insert((PairElem::Agent(idx_agent_a), PairElem::Agent(idx_agent_b)));

                (Some(idx_agent_a), Some(idx_agent_b))
            }
            (
                ActivePairMember::Agent {
                    name,
                    inactive_vars: _,
                },
                ActivePairMember::Var(v),
            ) => {
                let idx_agent_a = self.push_ast_agent(name);

                let name_idx = self.push_var(idx_agent_a, v);

                self.active_pairs
                    .insert((PairElem::Agent(idx_agent_a), PairElem::Var(name_idx)));

                (Some(idx_agent_a), None)
            }
            (
                ActivePairMember::Var(v),
                ActivePairMember::Agent {
                    name,
                    inactive_vars: _,
                },
            ) => {
                let idx_agent_a = self.push_ast_agent(name);

                let name_idx = self.push_var(idx_agent_a, v);

                self.active_pairs
                    .insert((PairElem::Var(name_idx), PairElem::Agent(idx_agent_a)));

                (None, Some(idx_agent_a))
            }
            (ActivePairMember::Var(v1), ActivePairMember::Var(v2)) => {
                let name_idx_1 = self.push_name(v1);
                let name_idx_2 = self.push_name(v2);

                self.active_pairs
                    .insert((PairElem::Var(name_idx_1), PairElem::Var(name_idx_2)));

                (Some(name_idx_1), Some(name_idx_2))
            }
        }
    }

    #[tracing::instrument]
    pub fn push_ast_agent(&mut self, name: VarName) -> usize {
        let idx = self.push_name(name);

        self.push_agent(idx)
    }

    pub fn push_var(&mut self, node_idx: usize, name: String) -> usize {
        let name_idx = self.push_name(name);
        self.agents[node_idx].ports.push(PairElem::Var(name_idx));

        name_idx
    }

    #[tracing::instrument]
    fn push_agent(&mut self, id: AgentId) -> usize {
        self.agents.push(Box::new(Agent {
            id,
            ports: Vec::new(),
        }));

        let id = self.agents.len() - 1;

        id
    }

    #[tracing::instrument]
    pub fn connect(&mut self, idx_a: usize, idx_b: usize) {
        if !self.agents[idx_a].ports.contains(&PairElem::Agent(idx_b)) {
            self.agents[idx_a].ports.push(PairElem::Agent(idx_b));
        }

        if !self.agents[idx_b].ports.contains(&PairElem::Agent(idx_a)) {
            self.agents[idx_b].ports.push(PairElem::Agent(idx_a));
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Agent {
    pub id: AgentId,
    pub ports: Vec<PairElem>,
}

#[cfg(test)]
mod test {
    use super::{super::ast, *};
    use chumsky::Parser;
    use test_log::test;

    #[test]
    fn test_eval_exprs() {
        [
            (
                "identity",
                "x >< y => x ~ y
                 A ~ B",
                "A ~ B",
            ),
            (
                "identity_2",
                "x >< y => x ~ y
                 x ~ B",
                "x ~ B",
            ),
            (
                "addition",
                "Add[x, y] >< Z => x ~ y
                 S[x] >< Add[y, z] => Add[y, S[z]] ~ x
                 Add[Z, y] ~ Z",
                "y ~ Z",
            ),
            (
                "addition_complex",
                "Add[x, y] >< Z => x ~ y
                 S[x] >< Add[y, z] => Add[y, S[z]] ~ x
                 S[Z] ~ Add[y, Z]",
                "y ~ S[Z]",
            ),
            (
                "addition_complex",
                "Add[x, y] >< Z => x ~ y
                 S[x] >< Add[y, z] => Add[y, S[z]] ~ x
                 S[Z] ~ Add[y, S[Z]]",
                "y ~ S[S[Z]]",
            ),
        ]
        .iter()
        .map(|(name, src, expected_evaluation)| {
            (
                name,
                ast::parser().parse(*src).unwrap(),
                ast::parser().parse(*expected_evaluation).unwrap(),
            )
        })
        .for_each(|(name, e, expected_eval)| {
            let (rules, instance) = e.to_application().unwrap();
            let (rule_nets, instance_n) = build_application_net(rules, instance).unwrap();

            let expected_instance_net =
                build_instance_net(expected_eval.to_instance().unwrap().to_vec()).unwrap();

            let eval = &reduce_to_end_or_infinity(rule_nets.as_slice(), instance_n)[0];

            assert_eq!(
                expected_instance_net.to_string(),
                eval.to_string(),
                "{}: {} != {}",
                name,
                expected_instance_net,
                eval,
            );
        });
    }

    #[test]
    fn test_match_rule() {
        [
            ("identity", "x >< y => x ~ y
             x ~ y", "x >< y => x ~ y"),
            ("identity_advanced", "x >< y => x ~ y
             A ~ B", "x >< y => x ~ y"),
            ("addition", "Add[x, y] >< Z => x ~ y
             S[x] >< Add[y, z] => Add[y, S[z]] ~ x
             Add[Z, y] ~ Z", "Add[x, y] >< Z => x ~ y"),
            ("combinators", "Constr[a, b] >< Dup[c, d] => Dup[a, b] ~ c, Dup[d, e] ~ f, Constr[g, d] ~ h, Constr[i, j] ~ a
             Era >< Constr[a, b] => Era ~ a, Era ~ b
             Era >< Dup[a, b] => Era ~ a, Era ~ b
             Constr[a, b] >< Constr[c, d] => a ~ b, c ~ d
             Dup[a, b] >< Dup[c, d] => a ~ c, b ~ d
             Era >< Era => ()
             Era ~ Era", "Era >< Era => ()"),
        ]
        .iter()
        .map(|(name, src, expected_rule)| (name, ast::parser().parse(*src).unwrap(), ast::parser().parse(*expected_rule).unwrap()))
        .for_each(|(name, e, expected_rule)| {
            let (rules, instance) = e.to_application().unwrap();
            let (rule_nets, mut instance_n) = build_application_net(rules, instance).unwrap();

            let rule = expected_rule.to_book();

            let mut rule_n_lhs = Net::default();
            let mut rule_n_rhs = Net::default();

            rule_n_lhs.push_net(rule[0].lhs.lhs.clone(), rule[0].lhs.rhs.clone());

            for member in rule[0].rhs.clone() {
                match member {
                    Instance::ActivePair(member) => {
                        rule_n_rhs.push_net(member.lhs, member.rhs);
                    }
                    _ => {}
                }
            }

            let redex = instance_n.active_pairs.pop_first().unwrap();

            let matches = matching_nets(rule_nets.as_slice(), &instance_n, redex.0, redex.1);

            assert_eq!((matches[0].0.to_string(), matches[0].1.to_string()), (rule_n_lhs.to_string(), rule_n_rhs.to_string()), "{}: {:?} != {:?}", name, (matches[0].0.to_string(), matches[0].1.to_string()), (rule_n_lhs.to_string(), rule_n_rhs.to_string()));
        });
    }

    #[test]
    fn test_expr_to_net() {
        [
            ("identity", "x >< y => x ~ y
             x ~ y"),
	    ("identity_2", "x >< y => x ~ y
             x ~ B"),
            ("addition", "Add[x, y] >< Z => x ~ y
             S[x] >< Add[y, z] => Add[y, S[z]] ~ x
             Add[Z, y] ~ Z"),
            ("combinators", "Constr[a, b] >< Dup[c, d] => Dup[a, b] ~ c, Dup[d, e] ~ f, Constr[g, d] ~ h, Constr[i, j] ~ a
             Era >< Constr[a, b] => Era ~ a, Era ~ b
             Era >< Dup[a, b] => Era ~ a, Era ~ b
             Constr[a, b] >< Constr[c, d] => a ~ b, c ~ d
             Dup[a, b] >< Dup[c, d] => a ~ c, b ~ d
             Era >< Era => ()
             Era ~ Era"),
        ].iter().map(|(name, src)| (name, ast::parser().parse(*src).unwrap())).for_each(|(name, e)| {
            let (_, instance) = e.to_application().unwrap();

            let mut instance_n = Net::default();
            instance_n.push_net(instance[0].as_active_pair().unwrap().lhs.clone(), instance[0].as_active_pair().unwrap().rhs.clone());

            assert_eq!(
                instance_n.to_string(),
                instance.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(", "),
                "{}: {} != {}",
                name,
                instance_n.to_string(),
                instance.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(", ")
            );
        });
    }

    #[test]
    fn test_simple_identity_reduction() {
        let e: Expr = ast::parser()
            .parse(
                "x >< y => x ~ y
                 x ~ y",
            )
            .unwrap();

        let res = reduce_expr_to_end_or_infinity(e)
            .into_iter()
            .map(|reduction| reduction.to_string())
            .collect::<Vec<_>>()
            .join(", ");

        assert_eq!(res, "x ~ y");
    }
}
