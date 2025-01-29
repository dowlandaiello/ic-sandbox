use std::{
    collections::{BTreeSet, VecDeque},
    fmt,
    iter::Iterator,
    marker::PhantomData,
    ops::{Deref, Range},
};

pub type Span = Range<usize>;

#[derive(Debug, Clone, Eq, Hash, PartialEq)]
pub struct Spanned<T: fmt::Debug>(pub T, pub Range<usize>);

impl<T: fmt::Debug> Deref for Spanned<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

pub trait TreeCursor<TValue>: Sized {
    fn hash(&self) -> usize;

    fn value(&self) -> TValue;

    fn children(&self) -> &mut dyn Iterator<Item = Self>;
}

pub struct TreeVisitor<TValue, TCursor: TreeCursor<TValue>> {
    to_visit: VecDeque<TCursor>,
    seen: BTreeSet<usize>,

    bruh: PhantomData<TValue>,
}

impl<TCursor: TreeCursor<TValue>, TValue> Iterator for TreeVisitor<TValue, TCursor> {
    type Item = TValue;

    fn next(&mut self) -> Option<Self::Item> {
        let mut next_items = self
            .to_visit
            .drain(..)
            .skip_while(|x| self.seen.contains(&x.hash()));
        let curr = next_items.next()?;

        self.to_visit = next_items.collect::<_>();

        self.seen.insert(curr.hash());

        self.to_visit
            .extend(curr.children().filter(|x| !self.seen.contains(&x.hash())));

        Some(curr.value())
    }
}
