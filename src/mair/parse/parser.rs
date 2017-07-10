use super::lexer::{Loc, TokenKind as Tokk, Token, LexSymbol as Sym};
use super::ast::{Delimiter, TT, TTKind};
use super::error::UnmatchedDelimError;

/// An iterator over `Token`s producing `TT`s
pub struct TTParser<I>(I);

enum NextTTResult<'a> {
    CloseDelim(Sym, Loc),
    TT(TT<'a>),
    Err(Loc),
    None,
}

impl<'a, I> TTParser<I>
        where I: Iterator<Item=Token<'a>> {
    pub fn new<T>(tokens: T) -> TTParser<I>
            where T: IntoIterator<IntoIter=I, Item=I::Item> {
        TTParser(tokens.into_iter())
    }

    /// Get the next TT or a close delimiter.
    fn next_tt(&mut self) -> NextTTResult<'a> {
        use self::NextTTResult as Ret;
        use self::Delimiter::*;
        use self::Sym::*;

        let (delim, close_delim, begin_pos) = match self.0.next() {
            None                           => return Ret::None,
            Some((Tokk::Symbol(sym), loc)) => match sym {
                LParen   => (Paren,   RParen,   loc.start),
                LBracket => (Bracket, RBracket, loc.start),
                LBrace   => (Brace,   RBrace,   loc.start),
                c@RParen   |
                c@RBracket |
                c@RBrace => return Ret::CloseDelim(c, loc),
                _        => return Ret::TT((TTKind::Token(Tokk::Symbol(sym)), loc)),
            },
            Some((tokk, loc))              => return Ret::TT((TTKind::Token(tokk), loc)),
        };
        let end_pos;
        let mut tts = vec![];
        loop {
            match self.next_tt() {
                Ret::CloseDelim(c, loc) => if c == close_delim {
                    end_pos = loc.end;
                    break;
                } else {
                    return Ret::Err(loc);
                },
                Ret::TT(tt)             => tts.push(tt),
                Ret::None               => return Ret::Err(begin_pos..(begin_pos + 1)),
                c                       => return c, // Ret::Err
            }
        }
        Ret::TT((TTKind::Tree{ delim, tts }, begin_pos..end_pos))
    }
}

impl<'a, I> Iterator for TTParser<I>
        where I: Iterator<Item=Token<'a>> {
    type Item = Result<TT<'a>, UnmatchedDelimError>;

    fn next(&mut self) -> Option<Self::Item> {
        use self::NextTTResult as Ret;
        match self.next_tt() {
            Ret::TT(tt)             => Some(Ok(tt)),
            Ret::None               => None,
            Ret::CloseDelim(_, loc) |
            Ret::Err(loc)           => Some(Err(UnmatchedDelimError(loc))),
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use super::super::lexer::test::lex;
    use self::Delimiter::*;

    fn parse_tt(input: &str) -> Result<Vec<TT>, UnmatchedDelimError> {
        let ltoks = lex(input).unwrap();
        let mut v = vec![];
        for c in TTParser::new(ltoks) {
            v.push(c?)
        }
        Ok(v)
    }

    #[test]
    fn tt_parser_test() {
        let star = |loc| (TTKind::Token(Tokk::Symbol(Sym::Mul)), loc);
        let tree = |delim, tts, loc| (TTKind::Tree{ delim, tts }, loc);
        assert_eq!(parse_tt(" "), Ok(vec![]));
        assert_eq!(parse_tt("*(* {*}[])"), Ok(vec![
            star(0..1),
            tree(Paren, vec![
                star(2..3),
                tree(Brace, vec![
                    star(5..6)
                ], 4..7),
                tree(Bracket, vec![], 7..9),
            ], 1..10),
        ]));
        let err = |loc| Err(UnmatchedDelimError(loc));
        assert_eq!(parse_tt(" ("),  err(1..2));
        assert_eq!(parse_tt("[("),  err(1..2));
        assert_eq!(parse_tt(" (]"), err(2..3));
    }

    #[test]
    fn tt_parser_large_input() {
        use std::fs::File;
        use std::io::Read;
        let mut source = String::new();
        File::open(file!()).unwrap().read_to_string(&mut source).unwrap();
        let ret = parse_tt(&source);
        println!("{:?}", ret);
        assert!(ret.is_ok());
    }
}
