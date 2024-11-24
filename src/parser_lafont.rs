use super::{
    ast_lafont::{Agent, Expr, Ident, Keyword, Net, Port, PortGrouping, PortKind, Token, Type},
    COMMENT_STR,
};
use chumsky::{
    error::Simple,
    prelude::*,
    text::{self, Character},
};
use std::{
    fmt,
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

pub fn lexer() -> impl Parser<char, Vec<Vec<Spanned<Token>>>, Error = Simple<char>> {
    let keyword = just::<char, _, _>("type")
        .map(|_| Token::Keyword(Keyword::Type))
        .or(just("symbol").map(|_| Token::Keyword(Keyword::Symbol)));
    let semicolon = just(";").map(|_| Token::Semicolon);
    let colon = just(":").map(|_| Token::Colon);
    let comma = just(",").map(|_| Token::Comma);
    let plus_output = just("+").map(|_| Token::PlusOutput);
    let minus_output = just("-").map(|_| Token::MinusInput);
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

pub fn parser() -> impl Parser<Spanned<Token>, Vec<Spanned<Expr>>, Error = Simple<Spanned<Token>>> {
    let span_just = move |val: Token| {
        filter::<Spanned<Token>, _, Simple<Spanned<Token>>>(move |tok: &Spanned<Token>| {
            **tok == val
        })
    };

    let type_declarations = span_just(Token::Keyword(Keyword::Type))
        .ignored()
        .then(
            select! {
                Spanned(Token::Ident(s), span) => Spanned(Expr::TypeDec(Type(s)), span)
            }
            .separated_by(span_just(Token::Comma)),
        )
        .map(|(_, elems)| elems);
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

                let port_kind = span_just(Token::MinusInput)
                    .map(move |_| PortKind::Input(Type(ident_a.clone().0)))
                    .or(span_just(Token::PlusOutput)
                        .map(move |_| PortKind::Output(Type(ident_b.clone().0))));

                let port_grouping = span_just(Token::NonDiscPartStart)
                    .ignored()
                    .then(port_kind.clone().separated_by(span_just(Token::Comma)))
                    .then_ignore(span_just(Token::NonDiscPartEnd))
                    .map(|(_, ps)| PortGrouping::Partition(ps));

                port_kind
                    .map(|p| PortGrouping::Singleton(p))
                    .or(port_grouping)
                    .separated_by(span_just(Token::Comma))
            })
            .separated_by(span_just(Token::Comma)),
        )
        .map(|((_, symbol), ports)| {
            Spanned(
                Expr::Symbol {
                    ident: symbol.clone().0,
                    ports: ports.into_iter().flatten().collect(),
                },
                symbol.clone().1,
            )
        });
    let agent = recursive(|expr| {
        select! {
            Spanned(Token::Ident(s), span) => Spanned(Ident(s), span)
        }
        .then_ignore(span_just(Token::LeftParen))
        .then(
            choice((
                expr.map(|agent: Spanned<Agent>| Spanned(Port::Agent(agent.0), agent.1)),
                select! {Spanned(Token::Ident(s), span) => Spanned(s, span)}
                    .map(|var_ident| Spanned(Port::Var(Ident(var_ident.0)), var_ident.1)),
            ))
            .separated_by(span_just(Token::Comma))
            .or_not(),
        )
        .then_ignore(span_just(Token::RightParen))
        .map(|(name, ports)| {
            Spanned(
                Agent {
                    name: name.0,
                    ports: ports
                        .unwrap_or_default()
                        .into_iter()
                        .map(|p| p.0)
                        .collect::<Vec<_>>(),
                },
                name.1,
            )
        })
    });
    let net = agent
        .clone()
        .map(|s| Spanned(Some(s.0), s.1))
        .or(span_just(Token::LeftParen)
            .then_ignore(span_just(Token::RightParen))
            .map(|s| Spanned(None, s.1)))
        .clone()
        .then_ignore(span_just(Token::ActivePair))
        .then(
            agent
                .map(|s| Spanned(Some(s.0), s.1))
                .or(span_just(Token::LeftParen)
                    .then_ignore(span_just(Token::RightParen))
                    .map(|s| Spanned(None, s.1))),
        )
        .map(
            |(lhs, rhs): (Spanned<Option<Agent>>, Spanned<Option<Agent>>)| {
                Spanned(
                    Expr::Net(Net {
                        lhs: lhs.0,
                        rhs: rhs.0,
                    }),
                    lhs.1,
                )
            },
        );

    choice((
        type_declarations,
        symbol_dec.map(|x| vec![x]),
        net.map(|x| vec![x]),
    ))
    .repeated()
    .flatten()
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_parser() {
        let cases = [(
            "type atom, list
             symbol P: atom+
             symbol O: atom+
             symbol L: atom+
             symbol Cons: list+, atom-, list-
             symbol Nil: list+
             symbol Append: list-, list-, list+
             Cons(x, Append(v, t)) >< Append(v, Cons(x, t))
             Nil() >< Append(v, v)",
            "type atom
type list
symbol P: atom+
symbol O: atom+
symbol L: atom+
symbol Cons: list+, atom-, list-
symbol Nil: list+
symbol Append: list-, list-, list+
Cons(x, Append(v, t)) >< Append(v, Cons(x, t))
Nil() >< Append(v, v)",
        )];

        for (case, expected) in cases {
            let lexed = lexer()
                .parse(case)
                .unwrap()
                .into_iter()
                .flatten()
                .collect::<Vec<_>>();
            let parsed = parser().parse(lexed).unwrap();

            assert_eq!(
                expected,
                parsed
                    .into_iter()
                    .map(|expr| expr.to_string())
                    .collect::<Vec<_>>()
                    .join("\n")
            );
        }
    }

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
