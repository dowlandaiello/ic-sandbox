use std::sync::atomic::{AtomicUsize, Ordering};

/// An iterator which generates a sequence of variable identifiers
#[derive(Debug, Default)]
pub struct NameIter {
    curr_var: AtomicUsize,
    curr_agent: AtomicUsize,
    curr_ident: AtomicUsize,
}

impl NameIter {
    pub fn starting_from(u: usize) -> Self {
        Self {
            curr_var: AtomicUsize::new(u),
            curr_agent: AtomicUsize::new(u),
            curr_ident: AtomicUsize::new(u),
        }
    }

    pub fn next_var_name(&self) -> String {
        let ident = self.curr_ident.fetch_add(1, Ordering::SeqCst).to_string();

        format!("v{}", ident)
    }

    pub fn next(&self) -> String {
        self.curr_var.fetch_add(1, Ordering::SeqCst).to_string()
    }

    pub fn next_var(&self) -> usize {
        self.curr_var.fetch_add(1, Ordering::SeqCst)
    }

    pub fn next_id(&self) -> usize {
        self.curr_agent.fetch_add(1, Ordering::SeqCst)
    }
}
