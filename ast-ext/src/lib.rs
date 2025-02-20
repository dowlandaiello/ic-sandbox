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

    fn children(&self) -> Box<dyn Iterator<Item = Self>>;
}

pub trait VisualDebug {
    fn node_id(&self) -> usize;

    fn node_label(&self) -> String;

    fn node_color(&self) -> String;

    fn conns(&self) -> impl Iterator<Item = String>;
}

pub struct TreeVisitor<TValue, TCursor: TreeCursor<TValue>> {
    to_visit: VecDeque<TCursor>,
    seen: BTreeSet<usize>,

    bruh: PhantomData<TValue>,
}

impl<TValue, TCursor> TreeVisitor<TValue, TCursor>
where
    TCursor: TreeCursor<TValue>,
    TValue: VisualDebug,
{
    pub fn into_string(self) -> String {
        let (nodes, conns): (Vec<String>, Vec<Vec<String>>) = self
            .map(|x| {
                (
                    format!(
                        "{} [shape=triangle color={} label=\"{}\"]",
                        x.node_id(),
                        x.node_color(),
                        x.node_label()
                    ),
                    (x.conns().collect::<Vec<_>>()),
                )
            })
            .collect();

        format!(
            "graph G {{
{}

{}
}}",
            nodes
                .into_iter()
                .map(|x| format!("{};", x))
                .collect::<Vec<_>>()
                .join("\n"),
            conns
                .into_iter()
                .flatten()
                .map(|x| format!("{};", x))
                .collect::<Vec<_>>()
                .join("\n")
        )
    }
}

impl<TCursor: TreeCursor<TValue>, TValue> TreeVisitor<TValue, TCursor> {
    pub fn new(init: TCursor) -> Self {
        Self {
            to_visit: [init].into(),
            seen: Default::default(),
            bruh: Default::default(),
        }
    }
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
