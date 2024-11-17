use super::ast::{ActivePairMember, Expr, Rule, RuleActivePair, VarName};
use std::{
    collections::{HashSet, LinkedList, VecDeque},
    fmt,
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
        Some((rules, instance)) => reduce_to_end_or_infinity(rules, instance),
        _ => Vec::new(),
    }
}

/// Reduces an expression to completion in the context of some rule.
pub fn reduce_to_end_or_infinity(nets: Vec<(Net, Net)>, instance_net: Net) -> Vec<RuleActivePair> {
    let mut results = Vec::new();
    let mut to_reduce = vec![instance_net];

    while let Some(curr_redex) = to_reduce.pop() {
        let new = if let Some(result) = reduce_net(nets.as_slice(), curr_redex.clone()) {
            result
        } else {
            break;
        };

        if new == curr_redex {
            results.push(new);

            break;
        };

        if new
            .active_pairs
            .iter()
            .filter(|(a, b)| matches!((a, b), (PairElem::Agent(_), PairElem::Agent(_))))
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

            let pair_a: HashSet<&str> =
                HashSet::from_iter(vec![lhs.get_name_for(agent_a), lhs.get_name_for(agent_b)]);
            let pair_b = HashSet::from_iter(vec![
                instance.get_name_for(&redex_lhs),
                instance.get_name_for(&redex_rhs),
            ]);

            if pair_a == pair_b || pair_a.is_subset(&pair_b) {
                return Some((lhs, rhs));
            }

            None
        })
        .collect::<Vec<_>>()
}

fn reduce_net(rules_nets: &[(Net, Net)], mut instance: Net) -> Option<Net> {
    tracing::debug!(
        "reducing net {} with next active pairs {:?}",
        instance,
        instance.active_pairs
    );

    let (redex_lhs, redex_rhs) = instance.active_pairs.pop_front()?;

    tracing::debug!("reducing active pair {:?} ~ {:?}", redex_lhs, redex_rhs);

    let (matching_rule, matching_replacement_ref) =
        matching_nets(rules_nets, &instance, redex_lhs.clone(), redex_rhs.clone()).remove(0);
    let mut matching_replacement = matching_replacement_ref.clone();

    tracing::debug!("matching rule candidate: {}", matching_rule);
    tracing::debug!("matching replacement candidate: {}", matching_replacement);

    // Replace vars and unwritten ports in rhs with nets in instance matching vars
    let to_replace = matching_replacement
        .agents
        .iter()
        .enumerate()
        .map(|(i, agent)| {
            agent
                .ports
                .iter()
                .enumerate()
                .filter(|(_, p)| p.as_ref().map(|p| p.is_var()).unwrap_or(true))
                .map(|(j, _)| (i, j))
                .collect::<Vec<_>>()
        })
        .flatten()
        .collect::<Vec<_>>();

    let replacements = [redex_lhs.clone(), redex_rhs.clone()]
        .into_iter()
        .map(|redex| match redex {
            PairElem::Agent(a) => instance.agents[a]
                .ports
                .iter()
                .enumerate()
                .skip(1)
                .filter(|(_, port)| port.as_ref().map(|p| p.is_var()).unwrap_or(true))
                .map(|(agent, port)| (agent, a, port))
                .collect::<Vec<_>>(),
            PairElem::Var(v) => {
                // Find the port and id of the agent to which this is connected
                unimplemented!()
            }
        })
        .flatten()
        .collect::<Vec<_>>();

    tracing::debug!(
        "replacing (agents, ports) {:?} with {:?} in net {:?}",
        to_replace,
        replacements,
        matching_replacement
    );

    /*

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
        matching_replacement.active_pairs = matching_replacement
        .active_pairs
        .into_iter()
        .filter(|(a, b)| a != &Some(agent_id_replace) && b != &Some(agent_id_replace))
        .collect();
        matching_replacement
        .active_pairs
        .push_front((Some(agent_id_replace), Some(id)));
    }
        None => {
        continue;
    }
    }
    }

         */

    None
}

#[derive(Debug, Default, Clone, PartialEq)]
pub struct Net {
    names: Vec<VarName>,
    agents: Vec<Box<Agent>>,
    active_pairs: LinkedList<(PairElem, PairElem)>,
}

#[derive(Debug, PartialEq, Clone)]
pub enum PairElem {
    Var(usize),
    Agent(usize),
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
                    PortElem::Var(v) => ActivePairMember::Var(self.names[v].clone()),
                    PortElem::Agent(port) => self.agent_to_pair_member(port.agent),
                })
                .collect::<Vec<_>>(),
        }
    }

    pub fn get_port(&self, node_a_idx: usize, port_idx: usize) -> &Option<PortElem> {
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
                    .push_front((PairElem::Agent(idx_agent_a), PairElem::Agent(idx_agent_b)));

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
                    .push_front((PairElem::Agent(idx_agent_a), PairElem::Var(name_idx)));

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
                    .push_front((PairElem::Agent(idx_agent_a), PairElem::Var(name_idx)));

                (None, Some(idx_agent_a))
            }
            (ActivePairMember::Var(v1), ActivePairMember::Var(v2)) => {
                let name_idx_1 = self.push_name(v1);
                let name_idx_2 = self.push_name(v2);

                self.active_pairs
                    .push_front((PairElem::Var(name_idx_1), PairElem::Var(name_idx_2)));

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
        self.agents[node_idx].ports[port_idx] = Some(PortElem::Var(name_idx));

        name_idx
    }

    #[tracing::instrument]
    fn push_agent(&mut self, id: AgentId, arity: usize) -> usize {
        self.agents.push(Box::new(Agent {
            id,
            ports: vec![None; arity],
        }));

        self.agents.len() - 1
    }

    #[tracing::instrument]
    pub fn connect(&mut self, idx_a: usize, port_a: usize, idx_b: usize, port_b: usize) {
        self.agents[idx_a].ports[port_a] = Some(PortElem::Agent(Box::new(Port {
            agent: idx_b,
            port_num: port_b,
        })));
        self.agents[idx_b].ports[port_b] = Some(PortElem::Agent(Box::new(Port {
            agent: idx_a,
            port_num: port_a,
        })));
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Agent {
    pub id: AgentId,
    pub ports: Vec<Option<PortElem>>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum PortElem {
    Agent(Box<Port>),
    Var(usize),
}

impl PortElem {
    pub fn is_var(&self) -> bool {
        matches!(self, PortElem::Var(_))
    }

    pub fn is_agent(&self) -> bool {
        matches!(self, PortElem::Agent(_))
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Port {
    pub port_num: usize,
    pub agent: AgentId,
}

#[cfg(test)]
mod test {
    use super::{super::ast, *};
    use chumsky::Parser;

    #[test]
    fn test_match_rule() {
        [
            ("identity", "x >< y => x ~ y
             x >< y", "x >< y => x ~ y"),
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

            let redex = instance_n.active_pairs.pop_front().unwrap();

            let matches = matching_nets(rule_nets.as_slice(), &instance_n, redex.0, redex.1);

	    assert_eq!((matches[0].0.to_string(), matches[0].1.to_string()), (rule_n_lhs.to_string(), rule_n_rhs.to_string()), "{}: {:?} != {:?}", name, (matches[0].0.to_string(), matches[0].1.to_string()), (rule_n_lhs.to_string(), rule_n_rhs.to_string()));
        });
    }

    #[test]
    fn test_expr_to_net() {
        [
            ("identity", "x >< y => x ~ y
             x >< y"),
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
