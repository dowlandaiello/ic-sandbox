use super::{
    ast_lafont::{Expr, Ident, Keyword, PortKind, Token, Type},
    COMMENT_STR,
};
use chumsky::{
    error::Simple,
    prelude::*,
    text::{self, Character},
};
use std::ops::{Deref, Range};

pub type Span = Range<usize>;

#[derive(Clone, Eq, Hash, PartialEq)]
pub struct Spanned<T>(T, Range<usize>);

impl<T> Deref for Spanned<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

pub fn lexer() -> impl Parser<char, Vec<Vec<Spanned<Token>>>, Error = Simple<char>> {
    let keyword = just::<char, _, _>("type")
        .map(|_| Token::Keyword(Keyword::Type))
        .or(just("symbol").map(|_| Token::Keyword(Keyword::Symbol)));
    let semicolon = just(";").map(|_| Token::Semicolon);
    let colon = just(":").map(|_| Token::Colon);
    let comma = just(",").map(|_| Token::Comma);
    let plus_output = just("+").map(|_| Token::PlusOutput);
    let minus_output = just("-").map(|_| Token::MinusInput);
    let unit = just("()").map(|_| Token::Unit);
    let non_disc_part_start = just("{{").map(|_| Token::NonDiscPartStart);
    let non_disc_part_end = just("}}").map(|_| Token::NonDiscPartEnd);
    let left_square_bracket = just("[").map(|_| Token::LeftSquareBracket);
    let right_square_bracket = just("]").map(|_| Token::RightSquareBracket);
    let left_paren = just("(").map(|_| Token::LeftParen);
    let right_paren = just(")").map(|_| Token::RightParen);
    let ident = text::ident().map(|s: String| Token::Ident(s.to_owned()));
    let active_pair = just("><").map(|_| Token::ActivePair);
    let comment = just(COMMENT_STR).then_ignore(text::newline().not().repeated());
    let inline_space = filter(Character::is_inline_whitespace);

    let token = choice((
        keyword,
        semicolon,
        colon,
        comma,
        plus_output,
        minus_output,
        unit,
        non_disc_part_start,
        non_disc_part_end,
        left_square_bracket,
        right_square_bracket,
        left_paren,
        right_paren,
        active_pair,
        ident,
    ));

    token
        .padded_by(inline_space.repeated().or_not())
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
}

pub fn parser() -> impl Parser<Spanned<Token>, Vec<Expr>, Error = Simple<Spanned<Token>>> {
    let span_just = move |val: Token| {
        filter::<Spanned<Token>, _, Simple<Spanned<Token>>>(move |tok: &Spanned<Token>| {
            **tok == val
        })
    };

    let type_declarations = span_just(Token::Keyword(Keyword::Type))
        .ignored()
        .then(select! {
            Spanned(Token::Ident(s), span) => Spanned(Expr::TypeDec(Type(s)), span)
        })
        .map(|(_, x)| x.0);
    let symbol_dec = span_just(Token::Keyword(Keyword::Symbol))
        .ignored()
        .then(select! {
            Spanned(Token::Ident(s), span) => Spanned(Ident(s), span)
        })
        .then_ignore(span_just(Token::Colon))
        .then(
            select! {
                Spanned(Token::Ident(s), span) => Spanned(s, span)
            }
            .then_with(move |ident| {
                let ident_a = ident.clone();
                let ident_b = ident.clone();

                span_just(Token::MinusInput)
                    .map(move |_| PortKind::Input(Type(ident_a.clone().0)))
                    .or(span_just(Token::PlusOutput)
                        .map(move |_| PortKind::Output(Type(ident_b.clone().0))))
            })
            .separated_by(span_just(Token::Comma)),
        )
        .map(|((_, symbol), ports)| Expr::Symbol {
            ident: symbol.clone().0,
            ports,
        });

    choice((type_declarations, symbol_dec)).repeated()
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_lex() {
        let cases = [(
            "type atom, list
             # This line has a comment
             symbol P: atom+

             # And this one
             symbol O: atom+

             # And this one

             symbol L: atom+
             symbol Cons: list+, atom-, list-
             symbol Nil: list+
             symbol Append: list-, list-, list+

             Cons(x, Append(v, t)) >< Append(v, Cons(x, t))
             Nil >< Append(v, v)",
            "type atom , list
symbol P : atom +
symbol O : atom +
symbol L : atom +
symbol Cons : list + , atom - , list -
symbol Nil : list +
symbol Append : list - , list - , list +
Cons ( x , Append ( v , t ) ) >< Append ( v , Cons ( x , t ) )
Nil >< Append ( v , v )",
        )];

        for (case, expected) in cases {
            assert_eq!(
                expected,
                lexer()
                    .parse(case)
                    .unwrap()
                    .iter()
                    .map(|tok| tok
                        .iter()
                        .map(|t| t.0.to_string())
                        .collect::<Vec<_>>()
                        .join(" "))
                    .collect::<Vec<_>>()
                    .join("\n"),
            );
        }
    }
}
