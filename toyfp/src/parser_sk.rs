use ast_ext::{Span, Spanned};
use chumsky::prelude::*;
use std::fmt;

#[derive(PartialEq, Eq, Clone, Debug)]
pub enum Expr {
    Call {
        callee: Box<Expr>,
        params: Vec<Expr>,
    },
    S,
    K,
    B,
    C,
    W,
    Var(String),
}

impl Expr {
    pub fn contains_var(&self, v: &str) -> bool {
        match self {
            Self::Call { callee, params } => {
                callee.contains_var(v) || params.iter().any(|x| x.contains_var(v))
            }
            Self::S | Self::K | Self::B | Self::C | Self::W => false,
            Self::Var(other) => v == other,
        }
    }
}

#[derive(Debug, Clone)]
pub enum SpannedExpr {
    Call {
        callee: Box<SpannedExpr>,
        params: Vec<SpannedExpr>,
    },
    S(Span),
    K(Span),
    B(Span),
    C(Span),
    W(Span),
    Var(Spanned<String>),
}

impl SpannedExpr {
    pub fn span(&self) -> &Span {
        match self {
            Self::Call { callee, .. } => callee.span(),
            Self::S(span) => span,
            Self::K(span) => span,
            Self::B(span) => span,
            Self::C(span) => span,
            Self::W(span) => span,
            Self::Var(Spanned(_, span)) => span,
        }
    }
}

impl From<SpannedExpr> for Spanned<Expr> {
    fn from(s: SpannedExpr) -> Self {
        match s {
            SpannedExpr::Call { callee, params } => {
                let span = callee.span().clone();
                let callee: Expr = (*callee).into();
                let params: Vec<Expr> = params.into_iter().map(|param| param.into()).collect();

                Self(
                    Expr::Call {
                        callee: Box::new(callee),
                        params,
                    },
                    span,
                )
            }
            SpannedExpr::S(span) => Self(Expr::S, span),
            SpannedExpr::K(span) => Self(Expr::K, span),
            SpannedExpr::B(span) => Self(Expr::B, span),
            SpannedExpr::C(span) => Self(Expr::C, span),
            SpannedExpr::W(span) => Self(Expr::W, span),
            SpannedExpr::Var(Spanned(x, span)) => Self(Expr::Var(x), span),
        }
    }
}

impl From<SpannedExpr> for Expr {
    fn from(s: SpannedExpr) -> Self {
        match s {
            SpannedExpr::Call { callee, params } => Self::Call {
                callee: Box::new((*callee).into()),
                params: params.into_iter().map(|param| param.into()).collect(),
            },
            SpannedExpr::S(_) => Self::S,
            SpannedExpr::K(_) => Self::K,
            SpannedExpr::B(_) => Self::B,
            SpannedExpr::C(_) => Self::C,
            SpannedExpr::W(_) => Self::W,
            SpannedExpr::Var(v) => Self::Var(v.0),
        }
    }
}

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::S => write!(f, "S"),
            Self::K => write!(f, "K"),
            Self::B => write!(f, "B"),
            Self::C => write!(f, "C"),
            Self::W => write!(f, "W"),
            Self::Var(v) => write!(f, "{}", v),
            Self::Call { callee, params } => write!(
                f,
                "({}{})",
                callee,
                params
                    .iter()
                    .map(|param| param.to_string())
                    .collect::<Vec<_>>()
                    .join("")
            ),
        }
    }
}

#[derive(Hash, Clone, Debug, Eq, PartialEq)]
pub enum Token {
    S,
    K,
    B,
    C,
    W,
    Ident(String),
    LeftParen,
    RightParen,
}

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::S => write!(f, "S"),
            Self::K => write!(f, "K"),
            Self::B => write!(f, "B"),
            Self::C => write!(f, "C"),
            Self::W => write!(f, "W"),
            Self::Ident(i) => write!(f, "{}", i),
            Self::LeftParen => write!(f, "("),
            Self::RightParen => write!(f, ")"),
        }
    }
}

pub fn lexer() -> impl Parser<char, Vec<Spanned<Token>>, Error = Simple<char>> {
    let s = just("S").map(|_| Token::S);
    let k = just("K").map(|_| Token::K);
    let b = just("B").map(|_| Token::B);
    let c = just("C").map(|_| Token::C);
    let w = just("W").map(|_| Token::W);
    let left_paren = just("(").map(|_| Token::LeftParen);
    let right_paren = just(")").map(|_| Token::RightParen);
    let ident = text::ident().map(|ident| Token::Ident(ident));

    choice((s, k, b, c, w, left_paren, right_paren, ident))
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
        let b = span_just(Token::B).map(|Spanned(_, span)| SpannedExpr::B(span));
        let c = span_just(Token::C).map(|Spanned(_, span)| SpannedExpr::C(span));
        let w = span_just(Token::W).map(|Spanned(_, span)| SpannedExpr::W(span));
        let left_paren = span_just(Token::LeftParen);
        let right_paren = span_just(Token::RightParen);
        let ident = select! {
            Spanned(Token::Ident(i), s) => Spanned(i, s)
        };

        let leaf = choice((
            k,
            s,
            b,
            c,
            w,
            ident.map(|Spanned(i, s)| SpannedExpr::Var(Spanned(i, s))),
        ));

        let call = left_paren
            .ignore_then(expr.clone().then(expr.clone().repeated().at_least(1)))
            .then_ignore(right_paren)
            .map(|(a, b)| SpannedExpr::Call {
                callee: Box::new(a),
                params: b,
            });

        choice((call, leaf))
    })
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_parse() {
        let cases = ["S", "K", "((SK)K)", "(SKK)"];

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

    #[test]
    fn test_parse_bckw() {
        let cases = ["K", "B", "C", "W", "(((CK)K)K)", "(CKKK)"];

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
