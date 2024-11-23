use super::{
    ast_lafont::{Keyword, Token},
    COMMENT_STR,
};
use chumsky::{error::Simple, prelude::*};
use std::ops::Range;

pub fn lex<'src>() -> impl Parser<&'src str, Vec<(Token, Range<usize>)>, Error = Simple<&'src str>>
{
    let keyword = just("type")
        .map(|_| Token::Keyword(Keyword::Type))
        .or(just("symbol").map(|_| Token::Keyword(Keyword::Symbol)));
    let semicolon = just(";").map(|_| Token::Semicolon);
    let colon = just(":").map(|_| Token::Colon);
    let plus_output = just("+").map(|_| Token::PlusOutput);
    let minus_output = just("-").map(|_| Token::MinusInput);
    let unit = just("()").map(|_| Token::Unit);
    let non_disc_part_start = just("{{").map(|_| Token::NonDiscPartStart);
    let non_disc_part_end = just("}}").map(|_| Token::NonDiscPartEnd);
    let left_square_bracket = just("[").map(|_| Token::LeftSquareBracket);
    let right_square_bracket = just("]").map(|_| Token::RightSquareBracket);
    let left_paren = just("(").map(|_| Token::LeftParen);
    let right_paren = just(")").map(|_| Token::RightParen);
    let ident = any().map(|s: &str| Token::Ident(s.to_owned()));

    let token = keyword
        .or(semicolon)
        .or(colon)
        .or(plus_output)
        .or(minus_output)
        .or(unit)
        .or(non_disc_part_start)
        .or(non_disc_part_end)
        .or(left_square_bracket)
        .or(right_square_bracket)
        .or(left_paren)
        .or(right_paren)
        .or(ident);

    let comment = just(COMMENT_STR).then_ignore(just("\n").not().repeated());

    token
        .map_with_span(|tok, e: Range<usize>| (tok, e))
        .padded_by(comment.repeated())
        .padded_by(just("\n"))
        .repeated()
}
