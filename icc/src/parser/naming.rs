/// An iterator which generates a sequence of variable identifiers
#[derive(Default)]
pub struct NameIter {
    curr_var: usize,
    curr_agent: usize,
    curr_ident: usize,
}

impl NameIter {
    pub fn next_var_name(&mut self) -> String {
        let ident = self.curr_ident.to_string();

        self.curr_ident += 1;

        format!("v{}", ident)
    }

    pub fn next(&mut self) -> String {
        let ident = self.curr_var.to_string();

        self.curr_var += 1;

        ident
    }

    pub fn next_var(&mut self) -> usize {
        let ident = self.curr_var;

        self.curr_var += 1;

        ident
    }

    pub fn next_id(&mut self) -> usize {
        let ident = self.curr_agent;

        self.curr_agent += 1;

        ident
    }
}
