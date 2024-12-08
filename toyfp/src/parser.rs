use ast_ext::{Span, Spanned};
use chumsky::prelude::*;
use std::fmt;

#[derive(Clone, Debug, PartialEq)]
pub enum Expr {
    Id(String),
    Abstraction { bind_id: String, body: Box<Expr> },
    Application { lhs: Box<Expr>, rhs: Box<Expr> },
}

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Id(s) => write!(f, "{}", s),
            Self::Abstraction { bind_id, body } => write!(f, "\\{}.{}", bind_id, body),
            Self::Application { lhs, rhs } => write!(f, "({})({})", lhs, rhs),
        }
    }
}

#[derive(Debug)]
pub enum Token {
    LeftParen,
    RightParen,
    Lambda,
    Ident(String),
    Dot,
}

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::LeftParen => write!(f, "("),
            Self::RightParen => write!(f, "("),
            Self::Lambda => write!(f, "\\"),
            Self::Ident(s) => write!(f, "{}", s),
            Self::Dot => write!(f, "."),
        }
    }
}

pub fn lexer() -> impl Parser<char, Vec<Spanned<Token>>, Error = Simple<char>> {
    let left_paren = just("(").map(|_| Token::LeftParen);
    let right_paren = just(")").map(|_| Token::RightParen);
    let lambda = just("\\").map(|_| Token::Lambda);
    let ident = text::ident().map(|s| Token::Ident(s));
    let dot = just(".").map(|_| Token::Dot);

    choice((left_paren, right_paren, lambda, ident, dot))
        .padded_by(text::whitespace())
        .map_with_span(|tok, e: Span| Spanned(tok, e))
        .repeated()
        .then_ignore(end())
}

pub fn parser() -> impl Parser<Spanned<Token>, Vec<Spanned<Expr>>, Error = Simple<Spanned<Token>>> {
}
