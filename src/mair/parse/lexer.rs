use std::ops::Range;
use std::collections::HashMap;
use regex::{Regex, escape};
use super::str_ptr_diff;

pub type Pos = usize;
pub type Loc = Range<Pos>;

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum TokenType {
    /// An inner document excluding comment tags. `//! ...` or `/*! ... */`.
    InnerDoc,
    /// An outer document excluding comment tags. `/// ...` or `/** ... */`.
    OuterDoc,
    /// An identifier, keyword or `_`.
    Ident,
    /// A lifetime excluding leading `'`.
    Lifetime,
    /// A char, string or number literal.
    Literal,
    /// A minimal symbol which never be the head of any compound symbol.
    Symbol(SymbolType),
    /// A symbol which may be the head of a compound symbol. Like `:` can be the head of `::`.
    /// Only be used for symbols followed by another symbol.
    HeadSymbol(SymbolType),
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum LexicalError<P> {
    UnknowToken(P),
    UnclosedComment(P),
    UnterminatedString(P),
}

impl<P> LexicalError<P> {
    fn map<NP, F>(self, f: F) -> LexicalError<NP>
            where F: FnOnce(P) -> NP {
        use self::LexicalError::*;
        match self {
            UnknowToken(p)      => UnknowToken(f(p)),
            UnclosedComment(p)  => UnclosedComment(f(p)),
            UnterminatedString(p)   => UnterminatedString(f(p)),
        }
    }
}

macro_rules! define_symbols(
    ($($cat:ident {$($tok:ident = $ch:expr;)+})+) => {
        #[derive(Debug, PartialEq, Eq, Clone, Copy)]
        enum SymbolCategory {
            $($cat,)+
        }

        #[derive(Debug, PartialEq, Eq, Clone, Copy)]
        pub enum SymbolType {
            $($($tok,)+)+
        }
        lazy_static! {
            static ref SYMBOLS: HashMap<&'static str, (SymbolCategory, SymbolType)> = {
                let mut m = HashMap::new();
                $($(m.insert($ch, (SymbolCategory::$cat, SymbolType::$tok));)+)+
                m
            };
            static ref RESTR_SYMBOLS: String = [$($(escape($ch),)+)+].join("|");
            static ref RE_SYMBOL: Regex = Regex::new(
                &format!(r"\A(?:{})", *RESTR_SYMBOLS)
            ).unwrap();
        }
     };
);

define_symbols!{
    Single {
        LBracket    = "[";
        RBracket    = "]";
        LParen      = "(";
        RParen      = ")";
        LBrace      = "{";
        RBrace      = "}";
        Comma       = ",";
        Semi        = ";";
        At          = "@";
        Hash        = "#";
        Dollar      = "$";
        Question    = "?";
    }
    Multi {
        Dot         = "."; // `..` `...`
        Colon       = ":"; // `::`

        Bang        = "!"; // `!=`

        Add         = "+"; // `+=`
        Sub         = "-"; // `-=`
        Mul         = "*"; // `*=`
        Div         = "/"; // `/=`
        Mod         = "%"; // `%=`

        And         = "&"; // `&&` `&=`
        Or          = "|"; // `||` `|=`
        Xor         = "^"; // `^=`

        Lt          = "<"; // `<=` `<<` `<<=`
        Gt          = ">"; // `>=` `>>` `>>=`

        Equ         = "="; // `==`
    }
} // define_symbols!

lazy_static! {
    static ref RE_MAIN: Regex = Regex::new(&format!(r#"(?xsm)\A(?:
        (?P<line_innerdoc>//!.*?$)|
        (?P<line_outerdoc>///(?:[^/].*?)??$)|
        (?P<line_comment>//.*?$)|
        (?P<block_innerdoc_beg>/\*!)|
        (?P<block_outerdoc_beg_eat1>/\*\*[^*/])|
        (?P<block_comment_beg>/\*)|
        (?P<num>\d[\d_]*(?:\.\d[\d_]*)?(?:[Ee][+-]?[\d_]+)?\w*)|    # TODO: verify 0b 0o 0x
        (?P<raw_string_beg>b?r(?P<raw_string_hashes>\#*)")|
        (?P<string>b?"[^"\\]*(?:\\.[^"\\]*)*(?P<string_closed>")?)|
        (?P<char>b?'(?:
            [[:^cntrl:]&&[^\\']]|
            \\(?:
                [\\'"nrt0]|
                x[[:xdigit:]]{{2}}|
                u\{{[[:xdigit:]]{{1,6}}\}}
            )
        )')|
        (?P<lifetime>'[A-Za-z_]\w*)|
        (?P<symbol>{})|
        (?P<ident>[A-Za-z_]\w*)
    )"#, *RESTR_SYMBOLS)).unwrap();
    static ref RE_BLOCK_COMMENT_BEGIN_END: Regex = Regex::new(
        r"(?s).*?(?:(?P<begin>/\*)|\*/)",
    ).unwrap();
}

/// An iterator over `str` producing `Some(TokenType)` for token or `None` for comment.
struct Tokenizer<'input> {
    rest: &'input str,
}

impl<'input> Tokenizer<'input> {
    pub fn new(input: &'input str) -> Self {
        Tokenizer{ rest: input }
    }

    fn advance(&mut self, len: usize) {
        assert!(len <= self.rest.len());
        self.rest = &self.rest[len..];
    }

    /// Consume block comment inner(without the starting tag) till the ending tag.
    fn eat_block_comment(&mut self) -> Result<(), LexicalError<()>> {
        let mut layer = 1;
        while layer > 0 {
            if let Some(cap) = RE_BLOCK_COMMENT_BEGIN_END.captures(&self.rest) {
                self.advance(cap[0].len());
                if cap.name("begin").is_some() {
                    layer += 1;
                } else {
                    layer -= 1;
                }
            } else {
                return Err(LexicalError::UnclosedComment(()));
            }
        }
        Ok(())
    }

    /// Consume raw string inner(without the starting tag) till the ending tag.
    fn eat_raw_string(&mut self, hashes: usize) -> Result<(), LexicalError<()>> {
        let pat = format!("\"{}", "#".repeat(hashes));
        if let Some(p) = self.rest.find(&pat) {
            self.advance(p + pat.len());
            Ok(())
        } else {
            Err(LexicalError::UnterminatedString(()))
        }
    }
}

impl<'input> Iterator for Tokenizer<'input> {
    type Item = Result<Option<(TokenType, &'input str)>, LexicalError<&'input str>>;

    fn next(&mut self) -> Option<Self::Item> {
        use self::TokenType::*;
        use self::LexicalError::*;

        let slast = self.rest.trim_left();
        self.rest = &slast;
        if self.rest.is_empty() {
            None
        } else if let Some(cap) = RE_MAIN.captures(&self.rest) {
            self.advance(cap[0].len());
            let is = |name| cap.name(name).is_some();
            let mut f = || -> Result<_, LexicalError<()>> {
                // wrap for the carriers inside
                Ok(match cap.get(0).unwrap().as_str() {
                    _ if is("line_innerdoc")        => Some(InnerDoc),
                    _ if is("line_outerdoc")        => Some(OuterDoc),
                    _ if is("line_comment")         => None,
                    _ if is("lifetime")             => Some(Lifetime),
                    _ if is("ident")                => Some(Ident),
                    _ if is("num") || is("char")    => Some(Literal),
                    _ if is("string")               => {
                        if is("string_closed") {
                            Some(Literal)
                        } else {
                            Err(UnterminatedString(()))?
                        }
                    },
                    _ if is("block_innerdoc_beg")   => {
                        self.eat_block_comment()?;
                        Some(InnerDoc)
                    },
                    _ if is("block_outerdoc_beg_eat1")  => {
                        self.rest = &slast[cap[0].len() - 1..]; // put the eaten first char back
                        self.eat_block_comment()?;
                        Some(OuterDoc)
                    },
                    _ if is("block_comment_beg")    => {
                        self.eat_block_comment()?;
                        None
                    },
                    _ if is("raw_string_beg")       => {
                        self.eat_raw_string(cap["raw_string_hashes"].len())?;
                        Some(Literal)
                    },
                    m if is("symbol")               => match SYMBOLS[m] {
                        (SymbolCategory::Multi, tokty) if RE_SYMBOL.is_match(&self.rest)
                                   => Some(HeadSymbol(tokty)),
                        (_, tokty) => Some(Symbol(tokty)),
                    },
                    _ => unreachable!(),
                })
            };
            match f() {
                Ok(None)        => Some(Ok(None)),
                Ok(Some(tokty)) => Some(Ok(Some((tokty, &slast[..slast.len() - self.rest.len()])))),
                Err(e)          => Some(Err(e.map(|()| slast))),
            }
        } else { // regex match fails
            Some(Err(UnknowToken(&self.rest)))
        }
    }
}

/// An iterator over `str` whose output is compatible with the lalrpop parser.
pub struct Lexer<'input> {
    source: &'input str,
    tokenizer: Tokenizer<'input>,
}

impl<'input> Lexer<'input> {
    pub fn new(input: &'input str) -> Self {
        Lexer{ source: input, tokenizer: Tokenizer::new(input) }
    }

    /// Get the start and end index of a subslice of `source`.
    /// Panic if `s` is not a subslice of `source`.
    fn pos(&self, s: &'input str) -> (usize, usize) {
        let p = str_ptr_diff(s, self.source);
        assert!(0 <= p && p as usize <= self.source.len());
        (p as usize, p as usize + s.len())
    }
}

impl<'input> Iterator for Lexer<'input> {
    type Item = Result<(Pos, TokenType, Pos), LexicalError<usize>>;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            return match self.tokenizer.next() {
                None                       => None,
                Some(Err(e))               => Some(Err(e.map(|s| self.pos(s).0))),
                Some(Ok(None))             => continue, // skip comment as space
                Some(Ok(Some((tokty, s)))) => {
                    let (beg, end) = self.pos(s);
                    Some(Ok((beg, tokty, end)))
                }
            }
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use self::TokenType::*;
    use self::LexicalError::*;

    fn lex(input: &str) -> Result<Vec<(TokenType, Loc)>, LexicalError<usize>> {
        let mut v = vec![];
        for c in Lexer::new(input) {
            let (l, tok, r) = c?;
            v.push((tok, l..r));
        }
        Ok(v)
    }

    #[test]
    fn lexer_ident() {
        assert_eq!(lex("a"),        Ok(vec![(Ident, 0..1)]));
        assert_eq!(lex("_"),        Ok(vec![(Ident, 0..1)]));
        assert_eq!(lex("a0__c_"),   Ok(vec![(Ident, 0..6)]));
        assert_eq!(lex("_9 a0"),    Ok(vec![(Ident, 0..2), (Ident, 3..5)]));
    }

    #[test]
    fn lexer_space_comment_doc() {
        assert_eq!(lex("     "),    Ok(vec![]));
        assert_eq!(lex(" /**/\t"),  Ok(vec![]));
        assert_eq!(lex("a/* */a"),  Ok(vec![(Ident, 0..1), (Ident, 6..7)]));
        assert_eq!(lex("a// /*a"),  Ok(vec![(Ident, 0..1)]));
        assert_eq!(lex("a//\na"),   Ok(vec![(Ident, 0..1), (Ident, 4..5)]));

        assert_eq!(lex("a/*/**/*/a"),                   Ok(vec![(Ident, 0..1), (Ident, 9..10)]));
        assert_eq!(lex("a/*/**//*/**/*/*/a"),           Ok(vec![(Ident, 0..1), (Ident, 17..18)]));
        assert_eq!(lex("a/*/*/*/*/**/*/*/*/*/a"),       Ok(vec![(Ident, 0..1), (Ident, 21..22)]));
        assert_eq!(lex(r#"a/*0/**/"/*'/*/ */*/#*/ a"#), Ok(vec![(Ident, 0..1), (Ident, 24..25)]));

        assert_eq!(lex(" /*"),                              Err(UnclosedComment(1)));
        assert_eq!(lex("/*/**/*//**"),                      Err(UnclosedComment(8)));
        assert_eq!(lex("/*/*! */"),                         Err(UnclosedComment(0)));
        assert_eq!(lex(r#"a/*0/**/"/*'/*//*/+*/#*/ a"#),    Err(UnclosedComment(1)));

        assert_eq!(lex("////"),     Ok(vec![]));
        assert_eq!(lex("//// a"),   Ok(vec![]));
        assert_eq!(lex("/***/"),    Ok(vec![]));
        assert_eq!(lex("/****/"),   Ok(vec![]));
        assert_eq!(lex("/*** */"),  Ok(vec![]));
        assert_eq!(lex("///"),      Ok(vec![(OuterDoc, 0..3)]));
        assert_eq!(lex("///a\nb"),  Ok(vec![(OuterDoc, 0..4), (Ident, 5..6)]));
        assert_eq!(lex("//!"),      Ok(vec![(InnerDoc, 0..3)]));
        assert_eq!(lex("//! x"),    Ok(vec![(InnerDoc, 0..5)]));
        assert_eq!(lex("/*! a */"), Ok(vec![(InnerDoc, 0..8)]));
        assert_eq!(lex("/** */"),   Ok(vec![(OuterDoc, 0..6)]));
        assert_eq!(lex("/*!*/"),    Ok(vec![(InnerDoc, 0..5)]));
    }

    #[test]
    fn lexer_literal_lifetime() {
        assert_eq!(lex("1"),            Ok(vec![(Literal, 0..1)]));
        assert_eq!(lex("1isize"),       Ok(vec![(Literal, 0..6)]));
        assert_eq!(lex("1__3_.2_8_"),   Ok(vec![(Literal, 0..10)]));
        assert_eq!(lex("1.2e3f32"),     Ok(vec![(Literal, 0..8)]));
        assert_eq!(lex("1.2e-3"),       Ok(vec![(Literal, 0..6)]));
        assert_eq!(lex("1e+3"),         Ok(vec![(Literal, 0..4)]));
        assert_eq!(lex("0xDeAdBeEf"),   Ok(vec![(Literal, 0..10)]));
        assert_eq!(lex("0o__1_07"),     Ok(vec![(Literal, 0..8)]));
        assert_eq!(lex("0b__1_01"),     Ok(vec![(Literal, 0..8)]));

        assert_eq!(lex("0b__1_02"),     Ok(vec![(Literal, 0..8)])); // TODO: verify

        assert_eq!(lex(r#" "\"" "#),        Ok(vec![(Literal, 1..5)]));
        assert_eq!(lex(r#" b" \" \" " "#),  Ok(vec![(Literal, 1..11)]));
        assert_eq!(lex(r#" r"\" "#),        Ok(vec![(Literal, 1..5)]));
        assert_eq!(lex(r##" r#"\"# "##),    Ok(vec![(Literal, 1..7)]));

        assert_eq!(lex(r#" "\" "#),         Err(UnterminatedString(1)));
        assert_eq!(lex(r#" br#"" "#),       Err(UnterminatedString(1)));

        assert_eq!(lex("'a'a"),             Ok(vec![(Literal, 0..3), (Ident, 3..4)]));
        assert_eq!(lex("'劲'"),             Ok(vec![(Literal, 0..2+"劲".len())]));
        assert_eq!(lex(r"'\x00'"),          Ok(vec![(Literal, 0..6)]));
        assert_eq!(lex(r"'\''"),            Ok(vec![(Literal, 0..4)]));
        assert_eq!(lex(r"'\\'"),            Ok(vec![(Literal, 0..4)]));
        assert_eq!(lex(r"'\u{99}'"),        Ok(vec![(Literal, 0..8)]));
        assert_eq!(lex(r"'\u{000000}'"),    Ok(vec![(Literal, 0..12)]));

        assert!(lex(r"'\u{}'") != Ok(vec![(Literal, 0..6)]));
        assert!(lex(r"'\x0'")  != Ok(vec![(Literal, 0..5)]));

        assert_eq!(lex("'a 'a"),    Ok(vec![(Lifetime, 0..2), (Lifetime, 3..5)]));
        assert_eq!(lex("'_1a"),     Ok(vec![(Lifetime, 0..4)]));
    }

    #[test]
    fn lexer_symbol() {
        let mut source = String::new();
        let mut expect = vec![];
        for (k, &(cat, symty)) in SYMBOLS.iter() {
            let tokty = match cat {
                SymbolCategory::Single => Symbol(symty),
                SymbolCategory::Multi  => HeadSymbol(symty),
            };
            expect.push((tokty, source.len()..source.len() + 1));
            source += &k;
            if symty == SymbolType::Div { // avoid `//`
                expect.push((Symbol(SymbolType::Equ), source.len()..source.len() + 1));
                source += "=";
            } else {
                expect.push((Symbol(symty), source.len()..source.len() + 1));
                source += &k;
            }
            source += " ";
        }
        println!("testing: `{}`", source);
        assert_eq!(lex(&source), Ok(expect));
    }

    #[test]
    fn lexer_large_input() {
        use std::fs::File;
        use std::io::Read;
        let mut source = String::new();
        File::open(file!()).unwrap().read_to_string(&mut source).unwrap();
        assert!(lex(&source).is_ok());
    }
}
