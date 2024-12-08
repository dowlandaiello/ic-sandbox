use chumsky::{prelude::*, primitive::Filter};
use std::{
    fmt, hash,
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

pub fn span_just<TToken: fmt::Debug + Eq + hash::Hash>(
    val: TToken,
) -> Filter<impl Fn(&Spanned<TToken>) -> bool, Simple<Spanned<TToken>>> {
    filter::<Spanned<TToken>, _, Simple<Spanned<TToken>>>(move |tok: &Spanned<TToken>| **tok == val)
}
