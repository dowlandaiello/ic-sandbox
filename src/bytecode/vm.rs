use super::{CallSignature, Op, Program, Ptr};
use crate::{heuristics::TypedProgram, parser::ast_lafont::Net};
use std::collections::{linked_list::LinkedList, BTreeMap, HashSet};

pub enum StackElem {
    Ptr(Ptr),
    None,
    Instr(Op),
    Bool(bool),
}

/// An executor executes reduction steps on a program.
/// It attempts reduction on any
pub struct Executor {
    // Hash of all input ports to an output agent, and their output
    // Gets added to as reductions are executed
    // TODO: implement this as an LRU cache
    pub evaluations: BTreeMap<CallSignature, Ptr>,

    pub p: Program,

    pub stack: LinkedList<StackElem>,
}

impl Executor {
    pub fn new(p: Program) -> Self {
        Self {
            evaluations: Default::default(),
            p,
            stack: Default::default(),
        }
    }

    /// Converts the program to a human-readable form
    pub fn readback(&self) -> TypedProgram {
        TypedProgram {
            types: self
                .p
                .reductions
                .iter()
                .fold(Default::default(), |mut acc, ((lhs, rhs), _)| {
                    acc.insert(lhs.ty.clone());
                    acc.insert(rhs.ty.clone());

                    acc
                }),
            symbol_declarations_for: self.p.reductions.iter().fold(
                Default::default(),
                |mut acc, ((lhs, rhs), _)| {
                    acc.insert(lhs.ty.clone(), lhs.ports.clone());
                    acc.insert(rhs.ty.clone(), rhs.ports.clone());

                    acc
                },
            ),
            nets: self
                .p
                .active_pairs
                .iter()
                .map(|(lhs, rhs)| Net {
                    lhs: Some(lhs.clone()),
                    rhs: Some(rhs.clone()),
                })
                .collect::<HashSet<_>>(),
        }
    }

    /// Steps the virtual machine until nothing in the stack is left to execute
    pub fn step_to_end(&mut self) {
        while !self.stack.is_empty() {
            self.step();
        }
    }

    /// Attempts to reduce the next redex which has a redex in the rulebook
    /// to reduce it
    pub fn step(&mut self) {
        // Check if we have a rule to reduce the redex
        if let Some(next_reduce) = self
            .p
            .active_pairs
            .iter()
            .filter(|(a, b)| {
                (|| {
                    Some(self.p.reductions.contains_key(&(
                        self.p.type_signature_for(&a)?,
                        self.p.type_signature_for(&b)?,
                    )))
                })()
                .unwrap_or(false)
            })
            .next()
        {}
    }
}
