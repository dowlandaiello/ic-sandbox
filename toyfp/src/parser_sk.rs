use ast_ext::{Span, Spanned};
use chumsky::prelude::*;
use std::fmt;

#[derive(Clone, Debug)]
pub enum Expr {
    S(Option<Box<Expr>>, Option<Box<Expr>>, Option<Box<Expr>>),
    K(Option<Box<Expr>>, Option<Box<Expr>>),
    Var(String),
}

impl Expr {
    pub(crate) fn with_push_argument(self, arg: Option<Box<Expr>>) -> Self {
        match self {
            Self::S(a, b, c) => {
                if a.is_none() {
                    return Self::S(arg, b, c);
                }

                if b.is_none() {
                    return Self::S(a, arg, c);
                }

                Self::S(a, b, arg)
            }
            Self::K(a, b) => {
                if a.is_none() {
                    return Self::K(arg, b);
                }

                Self::K(a, arg)
            }
            v @ Self::Var(_) => v,
        }
    }
}

#[derive(Debug)]
pub enum SpannedExpr {
    S {
        span: Span,
        a: Option<Box<SpannedExpr>>,
        b: Option<Box<SpannedExpr>>,
        c: Option<Box<SpannedExpr>>,
    },
    K {
        span: Span,
        a: Option<Box<SpannedExpr>>,
        b: Option<Box<SpannedExpr>>,
    },
    Var(Spanned<String>),
}

impl SpannedExpr {
    pub fn span(&self) -> &Span {
        match self {
            Self::S { span, .. } => span,
            Self::K { span, .. } => span,
            Self::Var(Spanned(_, span)) => span,
        }
    }
}

impl From<SpannedExpr> for Spanned<Expr> {
    fn from(s: SpannedExpr) -> Self {
        match s {
            SpannedExpr::S { a, b, c, span } => Self(
                Expr::S(
                    a.map(|x| Box::new((*x).into())),
                    b.map(|x| Box::new((*x).into())),
                    c.map(|x| Box::new((*x).into())),
                ),
                span,
            ),
            SpannedExpr::K { a, b, span } => Self(
                Expr::K(
                    a.map(|x| Box::new((*x).into())),
                    b.map(|x| Box::new((*x).into())),
                ),
                span,
            ),
            SpannedExpr::Var(Spanned(x, span)) => Self(Expr::Var(x), span),
        }
    }
}

impl From<SpannedExpr> for Expr {
    fn from(s: SpannedExpr) -> Self {
        match s {
            SpannedExpr::S { a, b, c, .. } => Self::S(
                a.map(|x| Box::new((*x).into())),
                b.map(|x| Box::new((*x).into())),
                c.map(|x| Box::new((*x).into())),
            ),
            SpannedExpr::K { a, b, .. } => Self::K(
                a.map(|x| Box::new((*x).into())),
                b.map(|x| Box::new((*x).into())),
            ),
            SpannedExpr::Var(v) => Self::Var(v.0),
        }
    }
}

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::S(x, y, z) => write!(
                f,
                "(S{}{}{})",
                x.as_ref().map(|x| x.to_string()).unwrap_or_default(),
                y.as_ref().map(|x| x.to_string()).unwrap_or_default(),
                z.as_ref().map(|x| x.to_string()).unwrap_or_default()
            ),
            Self::K(a, b) => write!(
                f,
                "(K{}{})",
                a.as_ref().map(|x| x.to_string()).unwrap_or_default(),
                b.as_ref().map(|x| x.to_string()).unwrap_or_default()
            ),
            Self::Var(v) => write!(f, "({})", v),
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
        let k = span_just(Token::K);
        let s = span_just(Token::S);
        let left_paren = span_just(Token::LeftParen);
        let right_paren = span_just(Token::RightParen);
        let ident = select! {
            Spanned(Token::Ident(i), s) => Spanned(i, s)
        };

        left_paren
            .then(choice((
                k.then(expr.clone().repeated())
                    .map(|(Spanned(_, s), args)| {
                        let mut args_iter = args.into_iter();

                        SpannedExpr::K {
                            span: s,
                            a: args_iter.next().map(|x: SpannedExpr| Box::new(x)),
                            b: args_iter.next().map(|x: SpannedExpr| Box::new(x)),
                        }
                    }),
                s.then(expr.repeated()).map(|(Spanned(_, s), args)| {
                    let mut args_iter = args.into_iter();

                    SpannedExpr::S {
                        span: s,
                        a: args_iter.next().map(|x: SpannedExpr| Box::new(x)),
                        b: args_iter.next().map(|x: SpannedExpr| Box::new(x)),
                        c: args_iter.next().map(|x: SpannedExpr| Box::new(x)),
                    }
                }),
                ident.map(|Spanned(i, s)| SpannedExpr::Var(Spanned(i, s))),
            )))
            .then(right_paren)
            .map(|((_, e), _)| e)
    })
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_parse() {
        let cases = ["(S)", "(K)", "(S(K)(K))", "(S(K)(K)(K))", "(S(K(S))(K)(K))"];

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
