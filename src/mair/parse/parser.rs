use super::lexer::{TokenKind as Tokk, Token};
use super::ast::{TT, TTKind};
use super::error::UnmatchedDelimError;

/// Parse tokens into `TT`s.
pub fn parse_tts<'a>(toks: &[Token<'a>]) -> Result<Vec<TT<'a>>, UnmatchedDelimError> {
    let (rest, tts) = parse_tts_helper(toks)?;
    match rest.first() {
        None                => Ok(tts),
        Some(&(_, ref loc)) => Err(UnmatchedDelimError(loc.clone())),
    }
}

fn parse_tts_helper<'a, 'b>(mut toks: &'b [Token<'a>])
        -> Result<(&'b [Token<'a>], Vec<TT<'a>>), UnmatchedDelimError> {
    let mut tts = vec![];
    loop {
        match toks.first() {
            None | Some(&(Tokk::Delimiter{ is_open: false, .. }, _)) =>
                return Ok((toks, tts)),
            Some(&(Tokk::Delimiter{ is_open: true, delim }, ref loc)) => {
                let (rest, tts_inner) = parse_tts_helper(&toks[1..])?;
                toks = rest;
                match toks.first() {
                    None => return Err(UnmatchedDelimError(loc.clone())),
                    Some(&(Tokk::Delimiter{ is_open: false, delim: delim2 }, ref loc2)) => {
                        toks = &toks[1..];
                        if delim == delim2 {
                            tts.push((TTKind::Tree{
                                tts: tts_inner,
                                delim,
                            }, loc.start..loc2.end));
                        } else {
                            return Err(UnmatchedDelimError(loc2.clone()));
                        }
                    },
                    Some(_) => unreachable!(), // parse_tts_helper() only stops
                                               // before close delimiter or EOF
                }
            },
            Some(&(ref tokk, ref loc)) => {
                toks = &toks[1..];
                tts.push((TTKind::Token(tokk.clone()), loc.clone()));
            },
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use super::super::lexer::test::lex;
    use super::super::lexer::SymbolType as Sym;
    use super::super::ast::Delimiter::*;

    fn tts(input: &str) -> Result<Vec<TT>, UnmatchedDelimError> {
        let ltoks = lex(input).unwrap();
        parse_tts(&ltoks)
    }

    #[test]
    fn tt_parser_test() {
        let star = |loc| (TTKind::Token(Tokk::Symbol(Sym::Mul)), loc);
        let tree = |delim, tts, loc| (TTKind::Tree{ delim, tts }, loc);
        assert_eq!(tts(" "), Ok(vec![]));
        assert_eq!(tts("*(* {*}[])"), Ok(vec![
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
        assert_eq!(tts(" ("),  err(1..2));
        assert_eq!(tts("[("),  err(1..2));
        assert_eq!(tts(" (]"), err(2..3));
    }

    #[test]
    fn tt_parser_large_input() {
        use std::fs::File;
        use std::io::Read;
        let mut source = String::new();
        File::open(file!()).unwrap().read_to_string(&mut source).unwrap();
        let ret = tts(&source);
        println!("{:?}", ret);
        assert!(ret.is_ok());
    }
}
