use super::lexer::{TokenKind as Tokk, SymbolType, Token};
use super::ast::*;
use super::error::UnmatchedDelimError;
use super::putback_stream::PutbackStream;
use self::Delimiter::*;

pub struct Parser<'t>(PutbackStream<TT<'t>>);

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

/// Parser a `.rs` file. It will never fail, and source with grammar errors will
/// be parsed into specific position (as TT) of AST.
pub fn parse_crate(tts: Vec<TT>) -> Mod {
    Parser::new(tts).eat_mod_end()
}

// Helper macros
macro_rules! tok {
    ($tok:pat) => { tok!($tok, _) };
    ($tok:pat, $loc:pat) => { (TTKind::Token($tok), $loc) };
}

macro_rules! tree {
    ($loc:pat, $($t:tt)*) => { (TTKind::Tree{$($t)*}, $loc) };
}

macro_rules! kw {
    ($s:tt) => { kw!($s, _) };
    ($s:tt, $loc:pat) => { tok!(Tokk::Keyword(keyword_type!($s)), $loc) };
}

macro_rules! sym {
    ($s:tt) => { sym!($s, _) };
    ($s:tt, $loc:pat) => { tok!(Tokk::Symbol(symbol_type!($s)), $loc) };
}

macro_rules! ident {
    ($p:pat) => { ident!($p, _) };
    ($p:pat, $loc:pat) => { tok!(Tokk::Ident($p), $loc) };
}

macro_rules! lt {
    ($p:pat) => { lt!($p, _) };
    ($p:pat, $loc:pat) => { tok!(Tokk::Lifetime($p), $loc) };
}

macro_rules! lit {
    ($p:pat) => { lit!($p, _) };
    ($p:pat, $loc:pat) => { tok!(Tokk::Literal($p), $loc) };
}

macro_rules! lit_str {
    () => { lit!(Literal::StrLike{ is_bytestr: false, .. }) };
    ($s:pat) => { lit_str!($s, _) };
    ($s:pat, $loc:pat) => {
        lit!(Literal::StrLike{ is_bytestr: false, s: $s }, $loc)
    };
}

impl<'t> Parser<'t> {
    pub fn new(tts: Vec<TT<'t>>) -> Self {
        Parser(PutbackStream::new(tts))
    }

    /// Take the rest of TTs.
    pub fn rest(self) -> Vec<TT<'t>> {
        self.0.rest()
    }

    /// Return whether there's no TT left.
    pub fn is_end(&self) -> bool {
        self.0.peek(0).is_none()
    }

    /// Eat and return many `p`s seperated by `sep` (without tailing `sep`)
    /// until `is_end` returns true. If the next TT after `p` is not `sep` , it
    /// will be converted by `err` and pushed into the result.
    fn eat_many<T, F, G, P>(
        &mut self,
        sep: SymbolType,
        mut is_end: F,
        mut err: G,
        mut p: P,
    ) -> Vec<T>
    where F: FnMut(&mut Self) -> bool,
          G: FnMut(TT<'t>) -> T,
          P: FnMut(&mut Self) -> T {
        if is_end(self) {
            return vec![];
        }
        let mut v = vec![];
        loop {
            v.push(p(self));
            'sep: loop {
                if is_end(self) {
                    return v;
                }
                match_eat!{ self.0;
                    tok!(Tokk::Symbol(sep_), loc) => if sep_ == sep {
                        break 'sep;
                    } else {
                        v.push(err((TTKind::Token(Tokk::Symbol(sep_)), loc)));
                    },
                    tok => v.push(err(tok)),
                    _ => return v, // no TT left
                }
            }
        }
    }

    /// Eat many `p`s seperated by `,` until the end. Return `p`s and whether
    /// it consumes tailing `,`.
    fn eat_many_comma_tail_end<T, G, P>(
        &mut self,
        err: G,
        p: P,
    ) -> (Vec<T>, bool)
    where G: FnMut(TT<'t>) -> T,
          P: FnMut(&mut Self) -> T {
        let mut tail = false;
        let v = self.eat_many(
            symbol_type!(","),
            |p_| match_eat!{ p_.0;
                t@sym!(",") => if p_.is_end() {
                    tail = true;
                    true
                } else {
                    p_.0.putback(t);
                    false
                },
                _ => p_.is_end(),
            },
            err,
            p,
        );
        (v, tail)
    }

    /// Eat inner attributes and then items to the end.
    pub fn eat_mod_end(&mut self) -> Mod<'t> {
        let inner_attrs = self.eat_inner_attrs();
        let mut items = vec![];
        while !self.is_end() {
            items.push(self.eat_item());
        }
        Mod{ inner_attrs, items }
    }

    /// Eat inner attributes as more as possible.
    fn eat_inner_attrs(&mut self) -> Vec<Attr<'t>> {
        let mut v = vec![];
        loop {
            match_eat!{ self.0;
                tok!(Tokk::InnerDoc(s)) => v.push(Attr::Doc(s)),
                sym!("#"), sym!("!"), tree!(_, delim: Bracket, tts) => {
                    let mut p = Parser::new(tts);
                    let meta = p.eat_meta();
                    v.push(Attr::Meta{ meta, unknow: p.rest() })
                },
                _ => return v,
            }
        }
    }

    /// Eat outer attributes as more as possible.
    fn eat_outer_attrs(&mut self) -> Vec<Attr<'t>> {
        let mut v = vec![];
        loop {
            match_eat!{ self.0;
                tok!(Tokk::OuterDoc(s)) => v.push(Attr::Doc(s)),
                sym!("#"), tree!(_, delim: Bracket, tts) => {
                    let mut p = Parser::new(tts);
                    let meta = p.eat_meta();
                    v.push(Attr::Meta{ meta, unknow: p.rest() })
                },
                _ => return v,
            }
        }
    }

    /// Eat a valid meta, or return Meta::Null without consuming any TT.
    fn eat_meta(&mut self) -> Meta<'t> {
        match_eat!{ self.0;
            ident!(key), sym!("="), lit!(value) =>
                Meta::KeyValue{ key, value },
            ident!(name), tree!(_, delim: Paren, tts) => {
                let mut p = Parser::new(tts);
                let (subs, _) = p.eat_many_comma_tail_end(
                    Meta::Unknow,
                    |p| p.eat_meta(),
                );
                Meta::Sub{ name, subs }
            },
            ident!(s) => Meta::Flag(s),
            _ => Meta::Null,
        }
    }

    /// Eat an item. It will consume at lease one TT.
    /// Warning: There must be at least one TT left.
    fn eat_item(&mut self) -> Item<'t> {
        let outer_attrs = self.eat_outer_attrs();
        let is_pub = match_eat!{ self.0;
            kw!("pub") => true,
            _ => false,
        };
        let opt_detail = self.eat_opt_item_detail();
        let detail = match opt_detail {
            Some(x) => x,
            None if outer_attrs.is_empty() && !is_pub => // havn't consumed
                match_eat!{ self.0;
                    tt => ItemKind::Unknow(tt),
                    _ => unreachable!(), // consumes nothing and nothing left
                },
            None => ItemKind::Null,
        };
        Item{ outer_attrs, is_pub, detail }
    }

    /// Eat and return the detail of an item, or return None.
    fn eat_opt_item_detail(&mut self) -> Option<ItemKind<'t>> {
        unimplemented!()
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use super::super::lexer::test::lex;
    use super::super::lexer::SymbolType as Sym;

    fn tts(input: &str) -> Result<Vec<TT>, UnmatchedDelimError> {
        let ltoks = lex(input).unwrap();
        parse_tts(&ltoks)
    }

    macro_rules! parse_check {
        ($s:expr, $f:ident, $ntt_rest:expr, $ret:expr) => {{
            let mut p = Parser::new(tts($s).unwrap());
            let r = p.$f();
            assert_eq!((r, p.rest().len()), ($ret, $ntt_rest));
        }};
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

    #[test]
    fn parser_meta() {
        let tok_dol = TTKind::Token(Tokk::Symbol(symbol_type!("$")));
        parse_check!("", eat_meta, 0, Meta::Null);
        parse_check!("a[]", eat_meta, 1, Meta::Flag("a"));
        parse_check!("a(a=1,$$,,)", eat_meta, 0, Meta::Sub{
            name: "a",
            subs: vec![
                Meta::KeyValue{
                    key: "a",
                    value: Literal::IntLike{ ty: None, val: 1 },
                },
                Meta::Null,
                Meta::Unknow((tok_dol.clone(), 6..7)),
                Meta::Unknow((tok_dol.clone(), 7..8)),
                Meta::Null,
            ],
        });
    }
}
