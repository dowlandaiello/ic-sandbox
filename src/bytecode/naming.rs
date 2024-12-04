use std::iter::Iterator;

/// An iterator which generates a sequence of variable identifiers
#[derive(Default)]
pub struct NameIter {
    curr: usize,
}

impl NameIter {
    pub fn next(&mut self) -> String {
        let ident = self.curr.to_string();

        self.curr += 1;

        ident
    }
}

impl Iterator for NameIter {
    type Item = String;

    fn next(&mut self) -> Option<Self::Item> {
        let ident = self.curr.to_string();

        self.curr += 1;

        Some(ident)
    }
}
