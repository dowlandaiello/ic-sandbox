use super::ast::{ActivePairMember, FreeVarId, Rule, RuleActivePair, VarName};
use std::{
    collections::{HashSet, LinkedList, VecDeque},
    fmt,
};

pub type AgentId = usize;

/// Reduces an expression to completion in the context of some rule.
pub fn reduce_to_end_or_infinity(
    rules: Vec<Rule>,
    instance: Vec<RuleActivePair>,
) -> Vec<RuleActivePair> {
    // Gather all nets representing rules
    let nets = rules
        .into_iter()
        .map(|rule| {
            let (mut net_lhs, mut net_rhs) = (Net::default(), Net::default());

            net_lhs.push_net(rule.lhs.lhs, rule.lhs.rhs);

            for member in rule.rhs {
                net_rhs.push_net(member.lhs, member.rhs);
            }

            (net_lhs, net_rhs)
        })
        .collect::<Vec<_>>();

    // Attempt reduction with all rules
    let mut to_reduce = instance
        .iter()
        .map(|instance| {
            let mut n = Net::default();
            n.push_net(instance.lhs.clone(), instance.rhs.clone());

            n
        })
        .collect::<Vec<_>>();
    let mut results = Vec::new();

    while let Some(curr_redex) = to_reduce.pop() {
        let new = if let Some(result) = reduce_net(nets.as_slice(), curr_redex.clone()) {
            result
        } else {
            break;
        };

        if !new
            .active_pairs
            .iter()
            .filter_map(|(a, b)| (*a).zip(*b))
            .count()
            > 0
        {
            to_reduce.push(new);
        } else {
            results.push(new);
        }
    }

    results
        .into_iter()
        .map(|n| <Net as Into<Vec<RuleActivePair>>>::into(n))
        .flatten()
        .collect::<Vec<_>>()
}

pub fn reduce_once(rules: Vec<Rule>, instance: Vec<RuleActivePair>) -> Option<Vec<RuleActivePair>> {
    // Gather all nets representing rules
    let nets = rules
        .into_iter()
        .map(|rule| {
            let (mut net_lhs, mut net_rhs) = (Net::default(), Net::default());

            net_lhs.push_net(rule.lhs.lhs, rule.lhs.rhs);

            for member in rule.rhs {
                net_rhs.push_net(member.lhs, member.rhs);
            }

            (net_lhs, net_rhs)
        })
        .collect::<Vec<_>>();

    // Attempt reduction with all rules
    let instance_net = {
        let mut n = Net::default();
        n.push_net(
            instance.iter().next()?.lhs.clone(),
            instance.iter().next()?.rhs.clone(),
        );

        n
    };

    reduce_net(nets.as_slice(), instance_net).map(|n| <Net as Into<Vec<RuleActivePair>>>::into(n))
}

fn reduce_net(rules_nets: &[(Net, Net)], mut instance: Net) -> Option<Net> {
    tracing::debug!(
        "reducing net {} with next active pairs {:?}",
        instance,
        instance.active_pairs
    );

    let (redex_lhs, redex_rhs) = instance.active_pairs.pop_front()?;
    let (redex_agent_a, redex_agent_b) =
        (&instance.agents[redex_lhs?], &instance.agents[redex_rhs?]);

    let (matching_rule, matching_replacement_ref) = rules_nets
        .iter()
        .filter_map(|(lhs, rhs)| {
            let (agent_a, agent_b) = lhs.active_pairs.iter().next()?;

            let pair_a: HashSet<&str> = HashSet::from_iter(vec![
                lhs.names[lhs.agents[(*agent_a)?].id].as_str(),
                lhs.names[lhs.agents[(*agent_b)?].id].as_str(),
            ]);
            let pair_b = HashSet::from_iter(vec![
                instance.names[redex_agent_a.id].as_str(),
                instance.names[redex_agent_b.id].as_str(),
            ]);

            if pair_a == pair_b {
                return Some((lhs, rhs));
            }

            None
        })
        .next()?;
    let mut matching_replacement = matching_replacement_ref.clone();

    tracing::debug!("matching rule candidate: {}", matching_rule);
    tracing::debug!("matching replacement candidate: {}", matching_replacement);

    // Replace vars in rhs with nets in instance matching vars
    let to_replace = matching_replacement
        .agents
        .iter()
        .enumerate()
        .map(|(i, agent)| {
            agent
                .ports
                .iter()
                .enumerate()
                .filter(|(_, p)| p.is_none())
                .map(|(j, _)| (i, j))
                .collect::<Vec<_>>()
        })
        .flatten()
        .collect::<Vec<_>>();

    let replacements = redex_agent_a
        .ports
        .iter()
        .skip(1)
        .chain(redex_agent_b.ports.iter().skip(1))
        .map(|port| port.clone().map(|p| instance.agents[p.agent].clone()))
        .collect::<Vec<_>>();

    tracing::debug!(
        "replacing (agents, ports) {:?} with {:?} in net {:?}",
        to_replace,
        replacements,
        matching_replacement
    );

    if replacements.len() != to_replace.len() {
        if to_replace.len() > 2 || replacements.len() > 2 {
            return None;
        }

        if replacements.len() == 1 {
            let agent = &replacements[0];

            // Insert the actual agent
            matching_replacement.push_agent(agent.as_ref()?.id, agent.as_ref()?.ports.len());

            return Some(matching_replacement);
        }

        match (&replacements[0]).as_ref().zip((&replacements[1]).as_ref()) {
            Some((redex_lhs, redex_rhs)) => {
                // Insert the actual agent
                let id_lhs = matching_replacement.push_agent(redex_lhs.id, redex_lhs.ports.len());
                let id_rhs = matching_replacement.push_agent(redex_rhs.id, redex_rhs.ports.len());

                // Connect all connected agents
                matching_replacement.connect(id_lhs, 0, id_rhs, 0);
            }
            _ => {
                return Some(matching_replacement);
            }
        }
    }

    // Work clockwise to replace ports
    for ((agent_id_replace, port_num_replace), replacement) in
        to_replace.into_iter().zip(replacements)
    {
        match replacement {
            Some(agent) => {
                // Insert the actual agent
                let id = matching_replacement
                    .push_ast_agent(instance.names[agent.id].clone(), agent.ports.len());

                // Connect all connected agents
                matching_replacement.connect(agent_id_replace, port_num_replace, id, 0);
            }
            None => {
                continue;
            }
        }
    }

    Some(matching_replacement)
}

#[derive(Debug, Default, Clone, PartialEq)]
pub struct Net {
    names: Vec<VarName>,
    agents: Vec<Box<Agent>>,
    active_pairs: LinkedList<(Option<usize>, Option<usize>)>,
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
        // Identity net
        if n.agents.len() == 0 {
            return vec![RuleActivePair {
                lhs: ActivePairMember::Var("x".to_string()),
                rhs: ActivePairMember::Var("y".to_string()),
            }];
        }

        n.active_pairs
            .iter()
            .enumerate()
            .map(|(i, (redex_lhs, redex_rhs))| RuleActivePair {
                lhs: redex_lhs
                    .map(|redex| {
                        n.agent_to_pair_member(redex, FreeVarId::prefixed(i.to_string()).next())
                    })
                    .unwrap_or(ActivePairMember::Var(
                        FreeVarId::prefixed(i.to_string()).next().0,
                    )),
                rhs: redex_rhs
                    .map(|redex| {
                        n.agent_to_pair_member(
                            redex,
                            FreeVarId::prefixed(i.to_string()).succ().next(),
                        )
                    })
                    .unwrap_or(ActivePairMember::Var(
                        FreeVarId::prefixed(i.to_string()).next().0,
                    )),
            })
            .collect::<Vec<_>>()
    }
}

impl Net {
    pub fn agent_to_pair_member(
        &self,
        agent_idx: usize,
        curr_free_var: FreeVarId,
    ) -> ActivePairMember {
        let a = &self.agents[agent_idx];

        ActivePairMember::Agent {
            name: self.names[a.id].clone(),
            inactive_vars: a
                .ports
                .iter()
                .skip(1)
                .enumerate()
                .map(|(i, maybe_p)| {
                    maybe_p
                        .as_ref()
                        .map(|port| {
                            self.agent_to_pair_member(
                                port.agent,
                                curr_free_var.prefix(i.to_string()).succ(),
                            )
                        })
                        .unwrap_or(ActivePairMember::Var(
                            curr_free_var.prefix(i.to_string()).0.clone(),
                        ))
                })
                .collect::<Vec<_>>(),
        }
    }

    pub fn get_port(&self, node_a_idx: usize, port_idx: usize) -> Option<&Port> {
        self.agents[node_a_idx].ports[port_idx].as_deref()
    }

    #[tracing::instrument]
    pub fn push_net(&mut self, lhs: ActivePairMember, rhs: ActivePairMember) {
        // Push and connect lhs and rhs
        let (lhs_loc, rhs_loc) = self.push_redex(lhs.clone(), rhs.clone());

        // Connect all aux ports to lhs and rhs
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
                            .map(|(i, member)| (id, self.agents[id].ports.len() + i, member))
                            .collect::<VecDeque<_>>(),
                    );
                }
                _ => {}
            }
        }
    }

    #[tracing::instrument]
    pub fn push_redex(
        &mut self,
        lhs: ActivePairMember,
        rhs: ActivePairMember,
    ) -> (Option<usize>, Option<usize>) {
        let lhs_loc = if let ActivePairMember::Agent {
            name,
            inactive_vars,
        } = lhs
        {
            Some(self.push_ast_agent(name, inactive_vars.len() + 1))
        } else {
            None
        };

        let rhs_loc = if let ActivePairMember::Agent {
            name,
            inactive_vars,
        } = rhs
        {
            Some(self.push_ast_agent(name, inactive_vars.len() + 1))
        } else {
            None
        };

        if let Some((lhs_loc, rhs_loc)) = lhs_loc.zip(rhs_loc) {
            self.connect(lhs_loc, 0, rhs_loc, 0);
        }

        self.active_pairs.push_front((lhs_loc, rhs_loc));

        (lhs_loc, rhs_loc)
    }

    #[tracing::instrument]
    pub fn push_ast_agent(&mut self, name: VarName, arity: usize) -> usize {
        let idx = self
            .names
            .iter()
            .position(|maybe_name| *maybe_name == *name)
            .unwrap_or_else(|| {
                self.names.push(name);
                self.names.len() - 1
            });

        self.push_agent(idx, arity)
    }

    #[tracing::instrument]
    pub fn push_agent(&mut self, id: AgentId, arity: usize) -> usize {
        self.agents.push(Box::new(Agent {
            id,
            ports: vec![None; arity],
        }));

        self.agents.len() - 1
    }

    #[tracing::instrument]
    pub fn connect(&mut self, idx_a: usize, port_a: usize, idx_b: usize, port_b: usize) {
        self.agents[idx_a].ports[port_a] = Some(Box::new(Port {
            agent: idx_b,
            port_num: port_b,
        }));
        self.agents[idx_b].ports[port_b] = Some(Box::new(Port {
            agent: idx_a,
            port_num: port_a,
        }));
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Agent {
    pub id: AgentId,
    pub ports: Vec<Option<Box<Port>>>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Port {
    pub port_num: usize,
    pub agent: AgentId,
}
