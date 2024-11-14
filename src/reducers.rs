use super::ast::{ActivePairMember, Rule, RuleActivePair, VarName};
use std::{
    collections::{LinkedList, VecDeque},
    hash::{DefaultHasher, Hash, Hasher},
};

pub type AgentId = usize;

#[derive(Default)]
pub struct Net {
    agents: Vec<Box<Agent>>,
    wires: Vec<Port>,
    active_pairs: LinkedList<(usize, usize)>,
}

impl Net {
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
            ports: Vec::with_capacity(arity),
            vals: Vec::with_capacity(arity),
        }));

        self.agents.len() - 1
    }

    pub fn connect(&mut self, idx_a: usize, port_a: usize, idx_b: usize, port_b: usize) {
        self.agents[idx_a].ports.push(Box::new(Port {
            agent: idx_b,
            port_num: port_b,
        }));
        self.agents[idx_b].ports.push(Box::new(Port {
            agent: idx_a,
            port_num: port_a,
        }));

        if port_a == 0 && port_b == 0 {
            self.active_pairs.push_front((idx_a, idx_b));
        }
    }
}

pub struct Agent {
    pub id: AgentId,
    pub ports: Vec<Box<Port>>,
    pub vals: Vec<Box<Val>>,
}

pub struct Port {
    pub port_num: usize,
    pub agent: AgentId,
}

pub enum Val {
    Char(char),
    I128(i128),
    I64(i64),
    I32(i32),
    I16(i16),
    I8(i8),
    U128(u128),
    U64(u64),
    U32(u32),
    U16(u16),
    U8(u8),
}

/// Reduces an expression to completion in the context of some rule.
pub fn reduce_to_end_or_infinity(rules: Vec<Rule>, instance: RuleActivePair) -> RuleActivePair {}
