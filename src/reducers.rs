use super::ast::{ActivePairMember, Expr, Rule, RuleActivePair, VarName};
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
                net_rhs.push_net(member.lhs, member.rhs);
            }

            (net_lhs, net_rhs)
        })
        .collect::<Vec<_>>()
}

pub fn build_instance_net(instance: Vec<RuleActivePair>) -> Option<Net> {
    let mut n = Net::default();

    n.push_net(
        instance.iter().next()?.lhs.clone(),
        instance.iter().next()?.rhs.clone(),
    );

    Some(n)
}

pub fn build_application_net(
    rules: Vec<Rule>,
    instance: Vec<RuleActivePair>,
) -> Option<(Vec<(Net, Net)>, Net)> {
    // Gather all nets representing rules
    let nets = build_book_net(rules);

    let n = build_instance_net(instance)?;

    Some((nets, n))
}

pub fn reduce_expr_to_end_or_infinity(e: Expr) -> Vec<RuleActivePair> {
    match e
        .to_application()
        .and_then(|(rules, instance)| build_application_net(rules, instance))
    {
        Some((rules, instance)) => reduce_to_end_or_infinity(&rules, instance),
        _ => Vec::new(),
    }
}

/// Reduces an expression to completion in the context of some rule.
pub fn reduce_to_end_or_infinity(nets: &[(Net, Net)], instance_net: Net) -> Vec<RuleActivePair> {
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
        .map(|n| <Net as Into<Vec<RuleActivePair>>>::into(n))
        .flatten()
        .collect::<Vec<_>>()
}

pub fn reduce_once(nets: Vec<(Net, Net)>, instance_net: Net) -> Option<Vec<RuleActivePair>> {
    reduce_net(nets.as_slice(), instance_net).map(|n| <Net as Into<Vec<RuleActivePair>>>::into(n))
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

fn reduce_net(rules_nets: &[(Net, Net)], mut instance: Net) -> Option<Net> {
    fn fmt_pair_elem(net: &Net, pair_elem: &PairElem) -> String {
        match pair_elem {
            PairElem::Var(v) => net.names[*v].clone(),
            PairElem::Agent(idx) => net.names[net.agents[*idx].id].clone(),
        }
    }

    // Work clockwise to replace ports
    fn fmt_replacement_target(net: &Net, target: &ReplacementTarget) -> String {
        match target {
            ReplacementTarget::WholeAgent { agent_idx } => {
                net.names[net.agents[*agent_idx].id].clone()
            }
            ReplacementTarget::WholeVar { var_idx } => net.names[*var_idx].clone(),
            ReplacementTarget::AgentPort { agent_idx, port } => format!(
                "{}[{} @ {}, ..]",
                net.names[net.agents[*agent_idx].id],
                net.agents[*agent_idx].ports[*port]
                    .as_ref()
                    .map(|port_elem| match port_elem {
                        PairElem::Agent(agent_idx) => fmt_replacement_target(
                            net,
                            &ReplacementTarget::WholeAgent {
                                agent_idx: *agent_idx
                            }
                        ),
                        PairElem::Var(var_idx) => fmt_replacement_target(
                            net,
                            &ReplacementTarget::WholeVar { var_idx: *var_idx }
                        ),
                    })
                    .unwrap_or("None".to_owned()),
                port
            ),
        }
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
    let mut matching_replacement = matching_replacement_ref.clone();

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
    // - Attached variables
    let to_replace = matching_replacement
        .active_pairs
        .iter()
        .map(|(a, b)| {
            [a.clone(), b.clone()]
                .into_iter()
                .filter_map(|redex| match redex {
                    PairElem::Var(v) => Some(ReplacementTarget::WholeVar { var_idx: v }),
                    _ => None,
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
                                .filter(|(_, port_elem)| {
                                    port_elem.as_ref().map(|p| p.is_var()).unwrap_or_default()
                                })
                                .map(|(i, _)| ReplacementTarget::AgentPort {
                                    agent_idx: a,
                                    port: i,
                                })
                                .collect::<Vec<_>>()
                        })
                        .flatten(),
                )
        })
        .flatten()
        .collect::<Vec<_>>();

    // Map of each replacement target to which node it is connected to
    let to_replace_conns = matching_replacement.active_pairs.clone();

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
                        .filter_map(|(_, port_elem)| port_elem.clone())
                        .collect::<Vec<_>>(),
                    PairElem::Var(_) => vec![],
                })
                .flatten(),
        )
        .chain(iter::once(redex_rhs.clone()));

    // Candidates must be replaced if:
    // - They are a variable
    // - They have no aux ports
    let mut replacements_unordered = replacement_candidates
        .enumerate()
        .filter(|(_, pair_elem)| match pair_elem {
            PairElem::Agent(idx) => instance.agents[*idx].ports.len() == 1,
            PairElem::Var(_) => true,
        })
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect::<Vec<_>>();
    replacements_unordered.sort_by_key(|(i, _)| *i);

    let replacements = replacements_unordered
        .into_iter()
        .map(|(_, x)| x)
        .collect::<Vec<_>>();

    tracing::debug!(
        "replacing (agents, ports) {} with {} in net {}",
        to_replace
            .iter()
            .map(|target| fmt_replacement_target(&matching_replacement, &target))
            .collect::<Vec<String>>()
            .join(", "),
        replacements
            .iter()
            .map(|target| fmt_pair_elem(&instance, &target))
            .collect::<Vec<String>>()
            .join(", "),
        matching_replacement
    );

    for (replacement_target, replacement_elem) in to_replace.into_iter().zip(replacements) {
        tracing::debug!(
            "replacing {} with {}",
            fmt_replacement_target(&matching_replacement, &replacement_target),
            fmt_pair_elem(&instance, &replacement_elem)
        );
        tracing::trace!(
            "replacing {:?} with {:?}",
            replacement_target,
            replacement_elem
        );

        match replacement_target {
            ReplacementTarget::AgentPort { agent_idx, port } => {
                // Insert the actual agent
                let id = match replacement_elem {
                    PairElem::Agent(p) => {
                        let idx = matching_replacement.push_ast_agent(
                            instance.names[instance.agents[p].id].clone(),
                            instance.agents[p].ports.len(),
                        );

                        replaced.insert(
                            matching_replacement.agents[agent_idx].ports[port]
                                .as_ref()?
                                .clone(),
                            PairElem::Agent(idx),
                        );

                        tracing::debug!(
                            "made replacement AgentPort {} -> Agent {}",
                            fmt_pair_elem(
                                &matching_replacement,
                                &matching_replacement.agents[agent_idx].ports[port]
                                    .as_ref()?
                                    .clone()
                            ),
                            fmt_pair_elem(&matching_replacement, &PairElem::Agent(idx))
                        );

                        idx
                    }
                    PairElem::Var(v) => {
                        let idx = matching_replacement.push_var(
                            agent_idx,
                            port,
                            instance.names[v].clone(),
                        );

                        replaced.insert(
                            matching_replacement.agents[agent_idx].ports[port]
                                .as_ref()?
                                .clone(),
                            PairElem::Var(idx),
                        );

                        tracing::debug!(
                            "made replacement AgentPort {} -> Var {}",
                            fmt_pair_elem(
                                &matching_replacement,
                                &matching_replacement.agents[agent_idx].ports[port]
                                    .as_ref()?
                                    .clone()
                            ),
                            fmt_pair_elem(&matching_replacement, &PairElem::Var(idx))
                        );

                        idx
                    }
                };

                // Connect all connected agents
                matching_replacement.connect(agent_idx, port, id, 0);
            }
            ReplacementTarget::WholeVar { var_idx } => {
                // We will always have to push a new agent
                match replacement_elem {
                    PairElem::Agent(p) => {
                        // Connect any connected nodes, if they exist (look for connections to this var idx)
                        let idx = matching_replacement.push_ast_agent(
                            instance.names[instance.agents[p].id].clone(),
                            instance.agents[p].ports.len(),
                        );

                        replaced.insert(PairElem::Var(var_idx), PairElem::Agent(idx));

                        tracing::debug!(
                            "made replacement WholeVar {} -> Agent {}",
                            fmt_pair_elem(&matching_replacement, &PairElem::Var(var_idx),),
                            fmt_pair_elem(&matching_replacement, &PairElem::Agent(idx))
                        );

                        matching_replacement
                            .agents
                            .iter()
                            .enumerate()
                            .map(|(i, agent)| {
                                agent
                                    .ports
                                    .iter()
                                    .enumerate()
                                    .filter(|(_, p)| {
                                        p.as_ref().map(|p| p.is_var()).unwrap_or_default()
                                            && p.as_ref()
                                                .map(|p| p.get_idx() == var_idx)
                                                .unwrap_or_default()
                                    })
                                    .map(|(p_idx, _)| (i, p_idx))
                                    .collect::<Vec<_>>()
                            })
                            .flatten()
                            .collect::<Vec<_>>()
                            .into_iter()
                            .for_each(|(agent_idx, var_port_idx)| {
                                matching_replacement.connect(idx, 0, agent_idx, var_port_idx)
                            });
                    }
                    PairElem::Var(v) => {
                        // Map indexes of connected nodes onto new indexes
                        // to enable active pair replacement

                        let idx = matching_replacement.push_name(instance.names[v].clone());

                        replaced.insert(PairElem::Var(var_idx), PairElem::Var(idx));

                        tracing::debug!(
                            "made replacement WholeVar {} -> Var {}",
                            fmt_pair_elem(&matching_replacement, &PairElem::Var(var_idx),),
                            fmt_pair_elem(&matching_replacement, &PairElem::Var(idx))
                        );
                    }
                };
            }
            ReplacementTarget::WholeAgent { agent_idx } => {
                match replacement_elem {
                    PairElem::Agent(p) => {
                        // Connect any connected nodes, if they exist (look for connections to this var idx)
                        let idx = matching_replacement.push_ast_agent(
                            instance.names[instance.agents[p].id].clone(),
                            instance.agents[p].ports.len(),
                        );

                        replaced.insert(PairElem::Agent(agent_idx), PairElem::Agent(idx));

                        tracing::debug!(
                            "made replacement WholeAgent {} -> Agent {}",
                            fmt_pair_elem(&matching_replacement, &PairElem::Agent(agent_idx)),
                            fmt_pair_elem(&matching_replacement, &PairElem::Agent(idx))
                        );

                        matching_replacement
                            .agents
                            .iter()
                            .enumerate()
                            .map(|(i, agent)| {
                                agent
                                    .ports
                                    .iter()
                                    .enumerate()
                                    .filter(|(_, p)| {
                                        p.as_ref().map(|p| p.is_agent()).unwrap_or_default()
                                            && p.as_ref()
                                                .map(|p| p.get_idx() == agent_idx)
                                                .unwrap_or_default()
                                    })
                                    .map(|(p_idx, _)| (i, p_idx))
                                    .collect::<Vec<_>>()
                            })
                            .flatten()
                            .collect::<Vec<_>>()
                            .into_iter()
                            .for_each(|(agent_idx, var_port_idx)| {
                                matching_replacement.connect(idx, 0, agent_idx, var_port_idx)
                            });
                    }
                    PairElem::Var(v) => {
                        // Map indexes of connected nodes onto new indexes
                        // to enable active pair replacement

                        let idx = matching_replacement.push_name(instance.names[v].clone());

                        replaced.insert(PairElem::Agent(agent_idx), PairElem::Var(idx));

                        tracing::debug!(
                            "made replacement WholeAgent {} -> Var {}",
                            fmt_pair_elem(&matching_replacement, &PairElem::Agent(agent_idx)),
                            fmt_pair_elem(&matching_replacement, &PairElem::Var(idx))
                        );
                    }
                }
            }
        }
    }

    tracing::debug!(
        "reduction resulted in replacements: {}",
        replaced
            .iter()
            .map(|(original, replaced)| format!(
                "{} -> {}",
                fmt_pair_elem(&matching_replacement, &original),
                fmt_pair_elem(&matching_replacement, &replaced)
            ))
            .collect::<Vec<String>>()
            .join(", ")
    );

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

    matching_replacement.active_pairs = to_replace_conns
        .into_iter()
        .map(|(target, connected_node)| {
            [
                replaced.get(&target).cloned().unwrap_or(target),
                replaced
                    .get(&connected_node)
                    .cloned()
                    .unwrap_or(connected_node),
            ]
            .into()
        })
        .collect::<BTreeSet<_>>()
        .into();

    tracing::debug!(
        "reduction resulted in {} {:?}",
        matching_replacement,
        matching_replacement
    );

    Some(matching_replacement)
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
        let pairs: Vec<RuleActivePair> = self.clone().into();

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

impl From<Net> for Vec<RuleActivePair> {
    fn from(n: Net) -> Self {
        n.active_pairs
            .iter()
            .map(|(redex_lhs, redex_rhs)| RuleActivePair {
                lhs: match redex_lhs {
                    PairElem::Var(v) => ActivePairMember::Var(n.names[*v].clone()),
                    PairElem::Agent(a) => n.agent_to_pair_member(*a),
                },
                rhs: match redex_rhs {
                    PairElem::Var(v) => ActivePairMember::Var(n.names[*v].clone()),
                    PairElem::Agent(a) => n.agent_to_pair_member(*a),
                },
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

    pub fn agent_to_pair_member(&self, agent_idx: usize) -> ActivePairMember {
        let a = &self.agents[agent_idx];

        ActivePairMember::Agent {
            name: self.names[a.id].clone(),
            inactive_vars: a
                .ports
                .iter()
                .skip(1)
                .filter_map(|p| p.clone())
                .map(|maybe_p| match maybe_p {
                    PairElem::Var(v) => ActivePairMember::Var(self.names[v].clone()),
                    PairElem::Agent(port) => self.agent_to_pair_member(port),
                })
                .collect::<Vec<_>>(),
        }
    }

    pub fn get_port(&self, node_a_idx: usize, port_idx: usize) -> &Option<PairElem> {
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

        while let Some((conn_agent_idx, conn_port, expr_insert)) = to_insert.pop_front() {
            match expr_insert {
                ActivePairMember::Agent {
                    name,
                    inactive_vars,
                } => {
                    let id = self.push_ast_agent(name.clone(), inactive_vars.len() + 1);
                    self.connect(id, 0, conn_agent_idx, conn_port);

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
                    self.push_var(conn_agent_idx, conn_port, v.clone());
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
                    inactive_vars: inactive_vars_lhs,
                },
                ActivePairMember::Agent {
                    name: name_rhs,
                    inactive_vars: inactive_vars_rhs,
                },
            ) => {
                let idx_agent_a = self.push_ast_agent(name_lhs, inactive_vars_lhs.len() + 1);
                let idx_agent_b = self.push_ast_agent(name_rhs, inactive_vars_rhs.len() + 1);

                self.connect(idx_agent_a, 0, idx_agent_b, 0);

                self.active_pairs
                    .insert((PairElem::Agent(idx_agent_a), PairElem::Agent(idx_agent_b)));

                (Some(idx_agent_a), Some(idx_agent_b))
            }
            (
                ActivePairMember::Agent {
                    name,
                    inactive_vars,
                },
                ActivePairMember::Var(v),
            ) => {
                let idx_agent_a = self.push_ast_agent(name, inactive_vars.len() + 1);

                let name_idx = self.push_var(idx_agent_a, 0, v);

                self.active_pairs
                    .insert((PairElem::Agent(idx_agent_a), PairElem::Var(name_idx)));

                (Some(idx_agent_a), None)
            }
            (
                ActivePairMember::Var(v),
                ActivePairMember::Agent {
                    name,
                    inactive_vars,
                },
            ) => {
                let idx_agent_a = self.push_ast_agent(name, inactive_vars.len() + 1);

                let name_idx = self.push_var(idx_agent_a, 0, v);

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
    pub fn push_ast_agent(&mut self, name: VarName, arity: usize) -> usize {
        let idx = self.push_name(name);

        self.push_agent(idx, arity)
    }

    pub fn push_var(&mut self, node_idx: usize, port_idx: usize, name: String) -> usize {
        let name_idx = self.push_name(name);
        self.agents[node_idx].ports[port_idx] = Some(PairElem::Var(name_idx));

        name_idx
    }

    #[tracing::instrument]
    fn push_agent(&mut self, id: AgentId, arity: usize) -> usize {
        self.agents.push(Box::new(Agent {
            id,
            ports: vec![None; arity],
        }));

        let id = self.agents.len() - 1;

        id
    }

    #[tracing::instrument]
    pub fn connect(&mut self, idx_a: usize, port_a: usize, idx_b: usize, port_b: usize) {
        self.agents[idx_a].ports[port_a] = Some(PairElem::Agent(idx_b));
        self.agents[idx_b].ports[port_b] = Some(PairElem::Agent(idx_a));
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Agent {
    pub id: AgentId,
    pub ports: Vec<Option<PairElem>>,
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
                 A >< B",
                "A >< B",
            ),
            (
                "identity_2",
                "x >< y => x ~ y
                 x >< B",
                "x >< B",
            ),
            (
                "addition",
                "Add[x, y] >< Z => x ~ y
                 S[x] >< Add[y, z] => Add[y, S[z]] ~ x
                 Add[Z, y] >< Z",
                "Z >< y",
            ),
            (
                "addition_complex",
                "Add[x, y] >< Z => x ~ y
                 S[x] >< Add[y, z] => Add[y, S[z]] ~ x
                 S[Z] >< Add[y, Z]",
                "S[Z] >< y",
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
                build_instance_net(expected_eval.to_instance().unwrap()).unwrap();

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
             x >< y", "x >< y => x ~ y"),
            ("identity_advanced", "x >< y => x ~ y
             A >< B", "x >< y => x ~ y"),
            ("addition", "Add[x, y] >< Z => x ~ y
             S[x] >< Add[y, z] => Add[y, S[z]] ~ x
             Add[Z, y] >< Z", "Add[x, y] >< Z => x ~ y"),
            ("combinators", "Constr[a, b] >< Dup[c, d] => Dup[a, b] ~ c, Dup[d, e] ~ f, Constr[g, d] ~ h, Constr[i, j] ~ a
             Era >< Constr[a, b] => Era ~ a, Era ~ b
             Era >< Dup[a, b] => Era ~ a, Era ~ b
             Constr[a, b] >< Constr[c, d] => a ~ b, c ~ d
             Dup[a, b] >< Dup[c, d] => a ~ c, b ~ d
             Era >< Era => ()
             Era >< Era", "Era >< Era => ()"),
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
                rule_n_rhs.push_net(member.lhs, member.rhs);
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
             x >< y"),
	    ("identity_2", "x >< y => x ~ y
             x >< B"),
            ("addition", "Add[x, y] >< Z => x ~ y
             S[x] >< Add[y, z] => Add[y, S[z]] ~ x
             Add[Z, y] >< Z"),
            ("combinators", "Constr[a, b] >< Dup[c, d] => Dup[a, b] ~ c, Dup[d, e] ~ f, Constr[g, d] ~ h, Constr[i, j] ~ a
             Era >< Constr[a, b] => Era ~ a, Era ~ b
             Era >< Dup[a, b] => Era ~ a, Era ~ b
             Constr[a, b] >< Constr[c, d] => a ~ b, c ~ d
             Dup[a, b] >< Dup[c, d] => a ~ c, b ~ d
             Era >< Era => ()
             Era >< Era"),
        ].iter().map(|(name, src)| (name, ast::parser().parse(*src).unwrap())).for_each(|(name, e)| {
            let (rules, instance) = e.to_application().unwrap();

            let mut instance_n = Net::default();
            instance_n.push_net(instance[0].lhs.clone(), instance[0].rhs.clone());

            assert_eq!(
                instance_n.to_string(),
                instance.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(", "),
                "{}: {} != {}",
                name,
                instance_n.to_string(),
                instance.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(", ")
            );

            rules.into_iter()
                .for_each(|rule| {
                    let (mut net_lhs, mut net_rhs) = (Net::default(), Net::default());

                    net_lhs.push_net(rule.lhs.lhs.clone(), rule.lhs.rhs.clone());

                    for member in rule.rhs {
                        net_rhs.push_net(member.lhs, member.rhs);
                    }

                    assert_eq!(
                        net_lhs.to_string(),
                        rule.lhs.to_string(),
                        "{}: {} != {}",
                        name,
                        net_lhs.to_string(),
                        rule.lhs.to_string()
                    );
                });
        });
    }

    #[test]
    fn test_simple_identity_reduction() {
        let e: Expr = ast::parser()
            .parse(
                "x >< y => x ~ y
                 x >< y",
            )
            .unwrap();

        let res = reduce_expr_to_end_or_infinity(e)
            .into_iter()
            .map(|reduction| reduction.to_string())
            .collect::<Vec<_>>()
            .join(", ");

        assert_eq!(res, "x >< y");
    }
}
