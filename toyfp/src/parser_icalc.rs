use ast_ext::{Span, Spanned};
use chumsky::prelude::*;

const COMMENT_STR: &str = "--";

#[derive(Clone, Eq, PartialEq, Hash, Debug)]
pub enum Token {
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

#[derive(Debug)]
pub enum Expr {
    Abstraction(Abstraction),
    Application(Application),
    Superposition(Superposition),
    Duplication(Duplication),
    Variable(Var),
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
        digit,
        equals,
        semi,
        ident,
    ));

    token
        .padded_by(text::whitespace().repeated().or_not())
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

pub fn parser() -> impl Parser<Spanned<Token>, Spanned<Expr>, Error = Simple<Spanned<Token>>> {
    let span_just = move |val: Token| {
        filter::<Spanned<Token>, _, Simple<Spanned<Token>>>(move |tok: &Spanned<Token>| {
            tok.0 == val
        })
    };

    let var = select! {
    Spanned(Token::Ident(i), s) => Spanned(Expr::Variable(Var(i)), s),
    };

    recursive(|expr| {
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
    })
}
