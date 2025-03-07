use ast_ext::{Span, Spanned};
use chumsky::prelude::*;
use std::fmt;

const COMMENT_STR: &str = "--";

#[derive(Clone, Debug, PartialEq)]
pub enum Stmt {
    Def { bind_name: String, def: Expr },
    Expr(Expr),
}

impl fmt::Display for Stmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Def { bind_name, def } => {
                write!(f, "{} = {}", bind_name, def)
            }
            Self::Expr(e) => {
                write!(f, "{}", e)
            }
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum Expr {
    Id(String),
    Abstraction { bind_id: String, body: Box<Expr> },
    Application { lhs: Box<Expr>, rhs: Box<Expr> },
}

impl Expr {
    pub fn as_id(&self) -> Option<&str> {
        match self {
            Self::Id(s) => Some(s),
            _ => None,
        }
    }
}

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Id(s) => write!(f, "{}", s),
            Self::Abstraction { bind_id, body } => write!(f, "\\{}.{}", bind_id, body),
            Self::Application { lhs, rhs } => {
                let lhs_repr = match lhs.as_ref() {
                    e @ &Self::Id(_) => format!("({})", e),
                    e @ &Self::Abstraction { .. } => format!("({})", e),
                    e @ &Self::Application { .. } => e.to_string(),
                };
                let rhs_repr = match rhs.as_ref() {
                    e @ &Self::Id(_) => format!("({})", e),
                    e @ &Self::Abstraction { .. } => format!("({})", e),
                    e @ &Self::Application { .. } => e.to_string(),
                };

                write!(f, "{}{}", lhs_repr, rhs_repr)
            }
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum Token {
    LeftParen,
    RightParen,
    Lambda,
    Ident(String),
    Dot,
    Eq,
}

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::LeftParen => write!(f, "("),
            Self::RightParen => write!(f, "("),
            Self::Lambda => write!(f, "\\"),
            Self::Ident(s) => write!(f, "{}", s),
            Self::Dot => write!(f, "."),
            Self::Eq => write!(f, "="),
        }
    }
}

pub fn lexer() -> impl Parser<char, Vec<Spanned<Token>>, Error = Simple<char>> {
    let comment = just(COMMENT_STR).then_ignore(text::newline().not().repeated());
    let left_paren = just("(").map(|_| Token::LeftParen);
    let right_paren = just(")").map(|_| Token::RightParen);
    let lambda = just("\\").map(|_| Token::Lambda);
    let ident = text::ident().map(|i| Token::Ident(i));
    let dot = just(".").map(|_| Token::Dot);
    let eq = just("=").map(|_| Token::Eq);

    let tok = choice((left_paren, right_paren, lambda, ident, dot, eq));

    tok.padded_by(text::whitespace())
        .map_with_span(|tok, e: Span| Spanned(tok, e))
        .repeated()
        .separated_by(
            comment
                .padded()
                .map(|_| ())
                .or(text::newline())
                .repeated()
                .at_least(1),
        )
        .allow_leading()
        .allow_trailing()
        .then_ignore(end())
        .flatten()
}

pub fn parser() -> impl Parser<Spanned<Token>, Vec<Spanned<Stmt>>, Error = Simple<Spanned<Token>>> {
    let span_just = move |val: Token| {
        filter::<Spanned<Token>, _, Simple<Spanned<Token>>>(move |tok: &Spanned<Token>| {
            tok.0 == val
        })
    };

    let id = select! {
    Spanned(Token::Ident(i), s) => Spanned(Expr::Id(i), s),
    };

    let expr = recursive(|expr| {
        let abstraction = span_just(Token::Lambda)
            .ignore_then(select! {
            Spanned(Token::Ident(i), s) => Spanned(i, s)
            })
            .then_ignore(span_just(Token::Dot))
            .then(expr.clone())
            .map(|(bind_id, body): (Spanned<String>, Spanned<Expr>)| {
                Spanned(
                    Expr::Abstraction {
                        bind_id: bind_id.0,
                        body: Box::new(body.0),
                    },
                    bind_id.1,
                )
            });
        let app_member = expr
            .clone()
            .delimited_by(span_just(Token::LeftParen), span_just(Token::RightParen));
        let application = app_member
            .clone()
            .then(app_member.clone().repeated().at_least(1))
            .foldl(|a: Spanned<Expr>, b: Spanned<Expr>| {
                Spanned(
                    Expr::Application {
                        lhs: Box::new(a.0),
                        rhs: Box::new(b.0),
                    },
                    a.1,
                )
            });

        choice((application, id, abstraction))
    });

    let def = select! {
    Spanned(Token::Ident(i), s) => Spanned(i, s)
    }
    .then_ignore(span_just(Token::Eq))
    .then(expr.clone())
    .map(|(bind, def)| {
        Spanned(
            Stmt::Def {
                bind_name: bind.0,
                def: def.0,
            },
            bind.1,
        )
    });

    def.repeated()
        .then(expr.map_with_span(|e, span: Span| Spanned(Stmt::Expr(e.0), span)))
        .map(|(mut defs, entry)| {
            defs.push(entry);

            defs
        })
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_parse_ok() {
        let cases = [
            ("a", "a"),
            ("(a)(b)", "(a)(b)"),
            ("\\a.a", "\\a.a"),
            ("\\f.x", "\\f.x"),
            ("(\\a.a)(a)", "(\\a.a)(a)"),
            ("(\\a.\\b.a)(c)(d)", "(\\a.\\b.a)(c)(d)"),
            (
                "id = \\x.x
(id)(x)",
                "id = \\x.x
(id)(x)",
            ),
        ];

        for (case, expected) in cases {
            assert_eq!(
                parser()
                    .parse(lexer().parse(case).unwrap())
                    .unwrap()
                    .iter()
                    .map(|stmt| stmt.to_string())
                    .collect::<Vec<_>>()
                    .join("\n"),
                expected
            );
        }
    }
}
