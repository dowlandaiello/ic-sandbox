use super::ast::{ActivePairMember, Rule, RuleActivePair, VarName};
use std::{
    collections::{LinkedList, VecDeque},
    hash::{DefaultHasher, Hash, Hasher},
};

pub type AgentId = usize;

/// Reduces an expression to completion in the context of some rule.
pub fn reduce_to_end_or_infinity(rules: Vec<Rule>, instance: RuleActivePair) -> RuleActivePair {
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

    let mut curr = instance;

    loop {
        // Attempt reduction with all rules
        let instance_net = {
            let mut n = Net::default();
            n.push_net(curr.lhs.clone(), curr.rhs.clone());

            n
        };

        let new = if let Some(result) = reduce(nets.as_slice(), instance_net) {
            result
        } else {
            break;
        };

        if &new == &curr {
            curr = new;

            break;
        }

        curr = new;
    }

    curr
}

fn reduce(rules_nets: &[(Net, Net)], mut instance: Net) -> Option<RuleActivePair> {
    let (redex_lhs, redex_rhs) = instance.active_pairs.pop_front()?;
    let (redex_agent_a, redex_agent_b) = (&instance.agents[redex_lhs], &instance.agents[redex_rhs]);

    let (_, matching_replacement_ref) = rules_nets
        .iter()
        .filter_map(|(lhs, rhs)| {
            let (agent_a, agent_b) = lhs.active_pairs.iter().next()?;

            if lhs.agents[*agent_a].id == redex_agent_a.id
                && lhs.agents[*agent_b].id == redex_agent_b.id
            {
                return Some((lhs, rhs));
            }

            None
        })
        .next()?;
    let mut matching_replacement = matching_replacement_ref.clone();

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

    if replacements.len() != to_replace.len() {
        return None;
    }

    // Work clockwise to replace ports
    for ((agent_id_replace, port_num_replace), replacement) in
        to_replace.into_iter().zip(replacements)
    {
        match replacement {
            Some(agent) => {
                // Insert the actual agent
                let id = matching_replacement.push_agent(agent.id, agent.ports.len());

                // Connect all connected agents
                matching_replacement.connect(agent_id_replace, port_num_replace, id, 1);
            }
            None => {
                continue;
            }
        }
    }

    None
}

#[derive(Default, Clone)]
pub struct Net {
    agents: Vec<Box<Agent>>,
    active_pairs: LinkedList<(usize, usize)>,
}

impl Net {
    pub fn get_port(&self, node_a_idx: usize, port_idx: usize) -> Option<&Port> {
        self.agents[node_a_idx].ports[port_idx].as_deref()
    }

    pub fn push_net(&mut self, lhs: ActivePairMember, rhs: ActivePairMember) {
        // Push and connect lhs and rhs
        let locs = self.push_redex(lhs.clone(), rhs.clone());
        let (lhs_loc, rhs_loc) = locs
            .0
            .zip(locs.1)
            .expect("redex active pairs were not inserted");

        // Connect all aux ports to lhs and rhs
        let mut to_insert = lhs
            .get_inactive_vars()
            .unwrap_or_default()
            .iter()
            .enumerate()
            .map(|(i, member)| (lhs_loc, self.agents[lhs_loc].ports.len() + i, member))
            .collect::<VecDeque<_>>();
        to_insert.extend(
            rhs.get_inactive_vars()
                .unwrap_or_default()
                .iter()
                .enumerate()
                .map(|(i, member)| (rhs_loc, self.agents[rhs_loc].ports.len() + i, member))
                .collect::<VecDeque<_>>(),
        );

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

        (lhs_loc, rhs_loc)
    }

    pub fn push_ast_agent(&mut self, name: VarName, arity: usize) -> usize {
        let mut s = DefaultHasher::new();
        name.hash(&mut s);

        self.push_agent(s.finish() as usize, arity)
    }

    pub fn push_agent(&mut self, id: AgentId, arity: usize) -> usize {
        self.agents.push(Box::new(Agent {
            id,
            ports: vec![None; arity],
        }));

        self.agents.len() - 1
    }

    pub fn connect(&mut self, idx_a: usize, port_a: usize, idx_b: usize, port_b: usize) {
        self.agents[idx_a].ports[port_a] = Some(Box::new(Port {
            agent: idx_b,
            port_num: port_b,
        }));
        self.agents[idx_b].ports[port_b] = Some(Box::new(Port {
            agent: idx_a,
            port_num: port_a,
        }));

        if port_a == 0 && port_b == 0 {
            self.active_pairs.push_front((idx_a, idx_b));
        }
    }
}

#[derive(Clone)]
pub struct Agent {
    pub id: AgentId,
    pub ports: Vec<Option<Box<Port>>>,
}

#[derive(Clone, PartialEq)]
pub struct Port {
    pub port_num: usize,
    pub agent: AgentId,
}
