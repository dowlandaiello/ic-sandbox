use ast_ext::{Span, Spanned};
use chumsky::prelude::*;
use std::fmt;

#[derive(Clone, Debug)]
pub enum Expr {
    Call(Box<Expr>, Box<Expr>),
    xS,
    K,
    Var(String),
}

#[derive(Debug)]
pub enum SpannedExpr {
    Call(Box<SpannedExpr>, Box<SpannedExpr>),
    S(Span),
    K(Span),
    Var(Spanned<String>),
}

impl SpannedExpr {
    pub fn span(&self) -> &Span {
        match self {
            Self::Call(lhs, _) => lhs.span(),
            Self::S(span) => span,
            Self::K(span) => span,
            Self::Var(Spanned(_, span)) => span,
        }
    }
}

impl From<SpannedExpr> for Spanned<Expr> {
    fn from(s: SpannedExpr) -> Self {
        match s {
            SpannedExpr::Call(a, b) => {
                let span = a.span().clone();
                let a_e: Expr = (*a).into();
                let b_e: Expr = (*b).into();

                Self(Expr::Call(Box::new(a_e), Box::new(b_e)), span)
            }
            SpannedExpr::S(span) => Self(Expr::S, span),
            SpannedExpr::K(span) => Self(Expr::K, span),
            SpannedExpr::Var(Spanned(x, span)) => Self(Expr::Var(x), span),
        }
    }
}

impl From<SpannedExpr> for Expr {
    fn from(s: SpannedExpr) -> Self {
        match s {
            SpannedExpr::Call(a, b) => Self::Call(Box::new((*a).into()), Box::new((*b).into())),
            SpannedExpr::S(_) => Self::S,
            SpannedExpr::K(_) => Self::K,
            SpannedExpr::Var(v) => Self::Var(v.0),
        }
    }
}

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::S => write!(f, "S"),
            Self::K => write!(f, "K"),
            Self::Var(v) => write!(f, "{}", v),
            Self::Call(a, b) => write!(f, "({}{})", a, b),
        }
    }
}

#[derive(Hash, Clone, Debug, Eq, PartialEq)]
pub enum Token {
    S,
    K,
    Ident(String),
    LeftParen,
    RightParen,
}

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::S => write!(f, "S"),
            Self::K => write!(f, "K"),
            Self::Ident(i) => write!(f, "{}", i),
            Self::LeftParen => write!(f, "("),
            Self::RightParen => write!(f, ")"),
        }
    }
}

pub fn lexer() -> impl Parser<char, Vec<Spanned<Token>>, Error = Simple<char>> {
    let s = just("S").map(|_| Token::S);
    let k = just("K").map(|_| Token::K);
    let left_paren = just("(").map(|_| Token::LeftParen);
    let right_paren = just(")").map(|_| Token::RightParen);
    let ident = text::ident().map(|ident| Token::Ident(ident));

    choice((s, k, left_paren, right_paren, ident))
        .padded_by(text::whitespace())
        .map_with_span(|tok, e: Span| Spanned(tok, e))
        .repeated()
        .then_ignore(end())
}

pub fn parser() -> impl Parser<Spanned<Token>, SpannedExpr, Error = Simple<Spanned<Token>>> {
    let span_just = move |val: Token| {
        filter::<Spanned<Token>, _, Simple<Spanned<Token>>>(move |tok: &Spanned<Token>| {
            **tok == val
        })
    };

    recursive(|expr| {
        let k = span_just(Token::K).map(|Spanned(_, span)| SpannedExpr::K(span));
        let s = span_just(Token::S).map(|Spanned(_, span)| SpannedExpr::S(span));
        let left_paren = span_just(Token::LeftParen);
        let right_paren = span_just(Token::RightParen);
        let ident = select! {
            Spanned(Token::Ident(i), s) => Spanned(i, s)
        };

        let leaf = choice((
            k,
            s,
            ident.map(|Spanned(i, s)| SpannedExpr::Var(Spanned(i, s))),
        ));

        let call = left_paren
            .ignore_then(
                expr.clone()
                    .then(expr)
                    .map(|(a, b)| SpannedExpr::Call(Box::new(a), Box::new(b))),
            )
            .then_ignore(right_paren);

        choice((call, leaf))
    })
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_parse() {
        let cases = ["S", "K", "((SK)K)"];

        for case in cases {
            let lexed = lexer().parse(case).unwrap();
            let parsed = parser().parse(lexed).unwrap();

            assert_eq!(
                <SpannedExpr as Into<Expr>>::into(parsed)
                    .to_string()
                    .as_str(),
                case
            );
        }
    }
}
