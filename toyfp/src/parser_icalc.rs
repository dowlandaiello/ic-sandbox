use ast_ext::{Span, Spanned};
use chumsky::prelude::*;
use std::fmt;

const COMMENT_STR: &str = "--";

#[derive(Clone, Eq, PartialEq, Hash, Debug)]
pub enum Token {
    Def,
    Lambda,
    LeftParen,
    RightParen,
    LeftBracket,
    RightBracket,
    Digit(usize),
    Equals,
    Semicolon,
    Ident(String),
    Dup,
}

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Def => write!(f, "def"),
            Self::Lambda => write!(f, "\\"),
            Self::LeftParen => write!(f, "("),
            Self::RightParen => write!(f, ")"),
            Self::LeftBracket => write!(f, "{{"),
            Self::RightBracket => write!(f, "}}"),
            Self::Digit(n) => write!(f, "{}", n),
            Self::Equals => write!(f, "="),
            Self::Semicolon => write!(f, ";"),
            Self::Ident(i) => write!(f, "{}", i),
            Self::Dup => write!(f, "dup"),
        }
    }
}

#[derive(Debug)]
pub enum Expr {
    Abstraction(Abstraction),
    Application(Application),
    Superposition(Superposition),
    Duplication(Duplication),
    Variable(Var),
}

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Abstraction(Abstraction { bind_var, body }) => {
                write!(f, "\\{} {}", bind_var, body)
            }
            Self::Application(Application(lhs, rhs)) => write!(f, "({} {})", lhs, rhs),
            Self::Superposition(Superposition(lhs, rhs)) => write!(f, "{{{} {}}}", lhs, rhs),
            Self::Duplication(Duplication {
                pair,
                to_clone,
                in_expr,
            }) => write!(
                f,
                "dup {{{} {}}} = {}; {}",
                pair.0, pair.1, to_clone, in_expr
            ),
            Self::Variable(v) => write!(f, "{}", v.0),
        }
    }
}

#[derive(Debug)]
pub enum Stmt {
    Def(Definition),
}

impl fmt::Display for Stmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Def(Definition { name, definition }) => {
                write!(f, "def {} = {}", name, definition)
            }
        }
    }
}

#[derive(Debug)]
pub struct Definition {
    pub name: String,
    pub definition: Expr,
}

#[derive(Debug)]
pub struct Abstraction {
    pub bind_var: String,
    pub body: Box<Expr>,
}

#[derive(Debug)]
pub struct Application(pub Box<Expr>, pub Box<Expr>);

#[derive(Debug)]
pub struct Superposition(pub Box<Expr>, pub Box<Expr>);

#[derive(Debug)]
pub struct Duplication {
    pub pair: (Box<String>, Box<String>),
    pub to_clone: Box<String>,
    pub in_expr: Box<Expr>,
}

#[derive(Debug)]
pub struct Var(pub String);

pub fn lexer() -> impl Parser<char, Vec<Vec<Spanned<Token>>>, Error = Simple<char>> {
    let comment = just(COMMENT_STR).then_ignore(text::newline().not().repeated());
    let def = just("def").map(|_| Token::Def);
    let left_bracket = just("{").map(|_| Token::LeftBracket);
    let right_bracket = just("}").map(|_| Token::RightBracket);
    let left_paren = just("(").map(|_| Token::LeftParen);
    let right_paren = just(")").map(|_| Token::RightParen);
    let lambda = just("\\").map(|_| Token::Lambda);
    let dup = just("dup").map(|_| Token::Dup);
    let digit = text::digits(10).map(|n: String| Token::Digit(n.parse().unwrap()));
    let equals = just("=").map(|_| Token::Equals);
    let semi = just(";").map(|_| Token::Semicolon);
    let ident = text::ident().map(|e| Token::Ident(e));

    let token = choice((
        left_bracket,
        right_bracket,
        left_paren,
        right_paren,
        lambda,
        dup,
        def,
        digit,
        equals,
        semi,
        ident,
    ));

    token
        .padded_by(text::whitespace().repeated())
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
}

pub fn parser() -> impl Parser<Spanned<Token>, Vec<Spanned<Stmt>>, Error = Simple<Spanned<Token>>> {
    let span_just = move |val: Token| {
        filter::<Spanned<Token>, _, Simple<Spanned<Token>>>(move |tok: &Spanned<Token>| {
            tok.0 == val
        })
    };

    let var = select! {
    Spanned(Token::Ident(i), s) => Spanned(Expr::Variable(Var(i)), s),
    };

    let expr = recursive(|expr| {
        let abstraction = span_just(Token::Lambda)
            .ignore_then(select! {
            Spanned(Token::Ident(i), s) => Spanned(i, s)
            })
            .then(expr.clone())
            .map(|(bind_id, body): (Spanned<String>, Spanned<Expr>)| {
                Spanned(
                    Expr::Abstraction(Abstraction {
                        bind_var: bind_id.0,
                        body: Box::new(body.0),
                    }),
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
                    Expr::Application(Application(Box::new(a.0), Box::new(b.0))),
                    a.1,
                )
            });
        let superposition = span_just(Token::LeftBracket)
            .ignore_then(expr.clone())
            .then(expr.clone())
            .then_ignore(span_just(Token::RightBracket))
            .map(|(a, b)| {
                Spanned(
                    Expr::Superposition(Superposition(Box::new(a.0), Box::new(b.0))),
                    a.1,
                )
            });
        let duplication = span_just(Token::Dup)
            .ignore_then(span_just(Token::LeftBracket))
            .ignore_then(select! {
                Spanned(Token::Ident(i), _) => i
            })
            .then(select! {
                    Spanned(Token::Ident(i), _) => i
            })
            .then_ignore(span_just(Token::Equals))
            .then(select! {Spanned(Token::Ident(i), _) => i})
            .then_ignore(span_just(Token::Semicolon))
            .then(expr)
            .map(|(((p, q), from), in_expr)| {
                Spanned(
                    Expr::Duplication(Duplication {
                        pair: (Box::new(p), Box::new(q)),
                        to_clone: Box::new(from),
                        in_expr: Box::new(in_expr.0),
                    }),
                    in_expr.1,
                )
            });

        choice((abstraction, application, superposition, duplication, var))
    });

    let stmt = select! {
    Spanned(Token::Ident(i), _) => i
    }
    .then_ignore(span_just(Token::Equals))
    .then(expr)
    .map(|(name, definition)| {
        Spanned(
            Stmt::Def(Definition {
                name,
                definition: definition.0,
            }),
            definition.1,
        )
    });

    stmt.repeated()
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_parse_simple() {
        let case = "def id = \\x x
";

        let lexed = lexer()
            .parse(case)
            .unwrap()
            .into_iter()
            .flatten()
            .collect::<Vec<_>>();

        assert_eq!(
            parser().parse(lexed).unwrap()[0].0.to_string(),
            case.to_string()
        );
    }
}
