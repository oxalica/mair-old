use std::ops::Range;
use std::collections::HashMap;
use regex::{Regex, escape};
use super::str_ptr_diff;

pub type Pos = usize;
pub type Loc = Range<Pos>;

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum LexToken<'input> {
    /// An inner document containing the content.
    InnerDoc(&'input str),
    /// An outer document containing the content.
    OuterDoc(&'input str),
    /// A keyword.
    Keyword(KeywordType),
    /// An identifier or `_`.
    Ident(&'input str),
    /// A lifetime excluding leading `'`.
    Lifetime(&'input str),
    /// A char, string or number literal.
    Literal(&'input str),
    /// A symbol.
    Symbol(LexSymbol),
    /// The ambiguous symbol `>` followed by `>` or `=`. eg. `>>` will be parsed into
    /// an `AmbigGt` and a normal `Symbol`, for that the first `>` can be either the end of
    /// template or a bitwise right shift operator when combining the following `>`.
    AmbigGt,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum LexicalError<P> {
    UnknowToken(P),
    UnclosedComment(P),
    UnterminatedString(P),
    InvalidNumberSuffix(P),
}

impl<P> LexicalError<P> {
    fn map<NP, F>(self, f: F) -> LexicalError<NP>
            where F: FnOnce(P) -> NP {
        use self::LexicalError::*;
        match self {
            UnknowToken(p)          => UnknowToken(f(p)),
            UnclosedComment(p)      => UnclosedComment(f(p)),
            UnterminatedString(p)   => UnterminatedString(f(p)),
            InvalidNumberSuffix(p)  => InvalidNumberSuffix(f(p)),
        }
    }
}

macro_rules! define_symbols(
    ($($tok:ident = $s:expr;)+) => {
        #[derive(Debug, PartialEq, Eq, Clone, Copy)]
        pub enum LexSymbol {
            $($tok,)+
        }

        lazy_static! {
            static ref SYMBOLS: HashMap<&'static str, LexSymbol> = {
                let mut m = HashMap::new();
                $(m.insert($s, LexSymbol::$tok);)+
                m
            };
            static ref RESTR_SYMBOLS: String = {
                let mut arr = [$($s,)+];
                arr.sort_by_key(|s| -(s.len() as isize));
                arr.iter().clone().map(|s| escape(s)).collect::<Vec<_>>().join("|")
            };
        }
     };
);

macro_rules! define_keywords {
    ($($kw:ident = $s:expr;)+) => {
        #[derive(Debug, PartialEq, Eq, Clone, Copy)]
        pub enum KeywordType {
            $($kw,)+
        }

        lazy_static! {
            static ref KEYWORDS: HashMap<&'static str, KeywordType> = {
                let mut m = HashMap::new();
                $(m.insert($s, KeywordType::$kw);)+
                m
            };
            static ref RESTR_KEYWORDS: String = [$(escape($s),)+].join("|");
        }
    };
}

define_symbols!{
    // https://doc.rust-lang.org/grammar.html#symbols
    // https://doc.rust-lang.org/grammar.html#unary-operator-expressions

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
    Dot         = ".";
    DotDot      = "..";
    DotDotDot   = "...";
    Colon       = ":";
    ColonColon  = "::";
    Bang        = "!";
    LArrow      = "<-";
    RArrow      = "->";
    RFatArrow   = "=>";

    Add         = "+";
    Sub         = "-";
    Mul         = "*";
    Div         = "/";
    Mod         = "%";
    And         = "&";
    Or          = "|";
    Xor         = "^";
    Shl         = "<<";
    // Shr         = ">>"; `Vec<Vec<_>>`
    AndAnd      = "&&";
    OrOr        = "||";
    EqEq        = "==";
    Ne          = "!=";
    Lt          = "<";
    Gt          = ">";
    Le          = "<=";
    // Ge          = ">="; `let _: Vec<_>=_;`
    Eq          = "=";
    AddEq       = "+=";
    SubEq       = "-=";
    MulEq       = "*=";
    DivEq       = "/=";
    ModEq       = "%=";
    AndEq       = "&=";
    OrEq        = "|=";
    XorEq       = "^=";
    ShlEq       = "<<=";
    // ShrEq       = ">>="; `let _: Vec<Vec<_>>=_;`
} // define_symbols!

lazy_static! {
    static ref RE_AMBIG_NEXT: Regex = Regex::new(
        r"\A(?:>|=)"
    ).unwrap();
}

define_keywords! {
    // https://doc.rust-lang.org/grammar.html#keywords
    KwAbstract  = "abstract";
    KwAlignof   = "alignof";
    KwAs        = "as";
    KwBecome    = "become";
    KwBox       = "box";
    KwBreak     = "break";
    KwConst     = "const";
    KwContinue  = "continue";
    KwCrate     = "crate";
    KwDo        = "do";
    KwElse      = "else";
    KwEnum      = "enum";
    KwExtern    = "extern";
    KwFalse     = "false";
    KwFinal     = "final";
    KwFn        = "fn";
    KwFor       = "for";
    KwIf        = "if";
    KwImpl      = "impl";
    KwIn        = "in";
    KwLet       = "let";
    KwLoop      = "loop";
    KwMacro     = "macro";
    KwMatch     = "match";
    KwMod       = "mod";
    KwMove      = "move";
    KwMut       = "mut";
    KwOffsetof  = "offsetof";
    KwOverride  = "override";
    KwPriv      = "priv";
    KwProc      = "proc";
    KwPub       = "pub";
    KwPure      = "pure";
    KwRef       = "ref";
    KwReturn    = "return";
    KwSelfTy    = "Self";
    KwSelfVar   = "self";
    KwSizeof    = "sizeof";
    KwStatic    = "static";
    KwStruct    = "struct";
    KwSuper     = "super";
    KwTrait     = "trait";
    KwTrue      = "true";
    KwType      = "type";
    KwTypeof    = "typeof";
    KwUnsafe    = "unsafe";
    KwUnsized   = "unsized";
    KwUse       = "use";
    KwVirtual   = "virtual";
    KwWhere     = "where";
    KwWhile     = "while";
    KwYield     = "yield";
} // define_keywords!

lazy_static! {
    static ref RE_MAIN: Regex = Regex::new(&format!(r#"(?xsm)\A(?:
        (?P<line_innerdoc>//!.*?(?:\z|\n))|
        (?P<line_outerdoc>///(?:[^/].*?)??(?:\z|\n))|
        (?P<line_comment>//.*?$)|
        (?P<block_innerdoc_beg>/\*!)|
        (?P<block_outerdoc_beg_eat1>/\*\*[^*/])|
        (?P<block_comment_beg>/\*)|
        (?P<num>
            (?:
                0b[01_]+|
                0o[0-7_]+|
                0x[[:xdigit:]]+|
                (?:
                    \d[\d_]*
                    (?:\.\d[\d_]*)?
                    (?:[Ee][+-]?[\d_]+)?
                )
            )
            (?P<num_suffix>\w*)
        )|
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
        (?P<symbol>{symbols})|
        (?P<keyword>(?:{keywords})\b)|
        (?P<ident>[A-Za-z_]\w*)
    )"#, symbols=*RESTR_SYMBOLS, keywords=*RESTR_KEYWORDS)).unwrap();

    static ref RE_BLOCK_COMMENT_BEGIN_END: Regex = Regex::new(
        r"(?s).*?(?:(?P<begin>/\*)|\*/)",
    ).unwrap();

    static ref RE_NUM_SUFFIX: Regex = Regex::new(
        r"(?x)\A(?:
            [iu](?:8|16|32|64|size)|
            f(?:32|64)
        )?\z"
    ).unwrap();
}

/// An iterator over `str` producing `Some(LexToken)` for token or `None` for comment.
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
    /// Return the comment content.
    fn eat_block_comment(&mut self) -> Result<&'input str, LexicalError<()>> {
        let sbegin = self.rest;
        let mut layer = 1;
        while layer > 0 {
            if let Some(cap) = RE_BLOCK_COMMENT_BEGIN_END.captures(self.rest) {
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
        Ok(&sbegin[..sbegin.len() - self.rest.len() - 2]) // excluding `*/`
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
    type Item = Result<Option<(LexToken<'input>, &'input str)>, LexicalError<&'input str>>;

    fn next(&mut self) -> Option<Self::Item> {
        use self::LexToken::*;
        use self::LexicalError::*;

        let slast = self.rest.trim_left();
        self.rest = slast;
        if self.rest.is_empty() {
            None
        } else if let Some(cap) = RE_MAIN.captures(self.rest) {
            self.advance(cap[0].len());
            let is = |name| cap.name(name).is_some();
            let mut f = || -> Result<_, LexicalError<()>> {
                // wrap for the carriers inside
                Ok(match cap.get(0).unwrap().as_str() {
                    m if is("line_innerdoc")        => Some(InnerDoc(&m[3..])),
                    m if is("line_outerdoc")        => Some(OuterDoc(&m[3..])),
                    _ if is("line_comment")         => None,
                    m if is("lifetime")             => Some(Lifetime(&m[1..])),
                    m if is("keyword")              => Some(Keyword(KEYWORDS[m])),
                    m if is("ident")                => Some(Ident(m)),
                    m if is("char")                 => Some(Literal(m)),
                    _ if is("block_innerdoc_beg")   => Some(InnerDoc(self.eat_block_comment()?)),
                    m if is("num")                  => {
                        if RE_NUM_SUFFIX.is_match(&cap["num_suffix"]) {
                            Some(Literal(m))
                        } else {
                            Err(InvalidNumberSuffix(()))?
                        }
                    },
                    m if is("string")               => {
                        if !is("string_closed") {
                            Err(UnterminatedString(()))?
                        } else {
                            Some(Literal(m))
                        }
                    },
                    _ if is("block_outerdoc_beg_eat1")  => {
                        self.rest = &slast[cap[0].len() - 1..]; // put the eaten first char back
                        Some(OuterDoc(self.eat_block_comment()?))
                    },
                    _ if is("block_comment_beg")    => {
                        self.eat_block_comment()?;
                        None
                    },
                    _ if is("raw_string_beg")       => {
                        self.eat_raw_string(cap["raw_string_hashes"].len())?;
                        Some(Literal(&slast[..slast.len() - self.rest.len()])) // including start/end tags
                    },
                    m if is("symbol")               => {
                        let tokty = SYMBOLS[m];
                        if tokty == LexSymbol::Gt && RE_AMBIG_NEXT.is_match(self.rest) {
                            Some(AmbigGt)
                        } else {
                            Some(Symbol(tokty))
                        }
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
            Some(Err(UnknowToken(self.rest)))
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
    type Item = Result<(Pos, LexToken<'input>, Pos), LexicalError<usize>>;

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
    use super::LexToken::*;
    use super::KeywordType::*;
    use super::LexSymbol::*;
    use super::LexicalError::*;

    fn lex(input: &str) -> Result<Vec<(LexToken, Loc)>, LexicalError<usize>> {
        let mut v = vec![];
        for c in Lexer::new(input) {
            let (l, tok, r) = c?;
            v.push((tok, l..r));
        }
        Ok(v)
    }

    #[test]
    fn lexer_keyword_ident() {
        assert_eq!(lex("_"),        Ok(vec![(Ident("_"), 0..1)]));
        assert_eq!(lex("a"),        Ok(vec![(Ident("a"), 0..1)]));
        assert_eq!(lex("as"),       Ok(vec![(Keyword(KwAs), 0..2)]));
        assert_eq!(lex("asc"),      Ok(vec![(Ident("asc"), 0..3)]));
        assert_eq!(lex("a0__c_"),   Ok(vec![(Ident("a0__c_"), 0..6)]));
        assert_eq!(lex("_9 a0"),    Ok(vec![(Ident("_9"), 0..2), (Ident("a0"), 3..5)]));
    }

    #[test]
    fn lexer_space_comment_doc() {
        assert_eq!(lex("     "),    Ok(vec![]));
        assert_eq!(lex(" /**/\t"),  Ok(vec![]));
        assert_eq!(lex("a/* */a"),  Ok(vec![(Ident("a"), 0..1), (Ident("a"), 6..7)]));
        assert_eq!(lex("a// /*a"),  Ok(vec![(Ident("a"), 0..1)]));
        assert_eq!(lex("a//\na"),   Ok(vec![(Ident("a"), 0..1), (Ident("a"), 4..5)]));

        assert_eq!(lex("a/*/**/*/a"),                   Ok(vec![(Ident("a"), 0..1), (Ident("a"), 9..10)]));
        assert_eq!(lex("a/*/**//*/**/*/*/a"),           Ok(vec![(Ident("a"), 0..1), (Ident("a"), 17..18)]));
        assert_eq!(lex("a/*/*/*/*/**/*/*/*/*/a"),       Ok(vec![(Ident("a"), 0..1), (Ident("a"), 21..22)]));
        assert_eq!(lex(r#"a/*0/**/"/*'/*/ */*/#*/ a"#), Ok(vec![(Ident("a"), 0..1), (Ident("a"), 24..25)]));

        assert_eq!(lex(" /*"),                              Err(UnclosedComment(1)));
        assert_eq!(lex("/*/**/*//**"),                      Err(UnclosedComment(8)));
        assert_eq!(lex("/*/*! */"),                         Err(UnclosedComment(0)));
        assert_eq!(lex(r#"a/*0/**/"/*'/*//*/+*/#*/ a"#),    Err(UnclosedComment(1)));

        assert_eq!(lex("////"),     Ok(vec![]));
        assert_eq!(lex("//// a"),   Ok(vec![]));
        assert_eq!(lex("/***/"),    Ok(vec![]));
        assert_eq!(lex("/****/"),   Ok(vec![]));
        assert_eq!(lex("/*** */"),  Ok(vec![]));
        assert_eq!(lex("///"),      Ok(vec![(OuterDoc(""), 0..3)]));
        assert_eq!(lex("///a\nb"),  Ok(vec![(OuterDoc("a\n"), 0..5), (Ident("b"), 5..6)]));
        assert_eq!(lex("//!\n"),    Ok(vec![(InnerDoc("\n"), 0..4)]));
        assert_eq!(lex("//! x"),    Ok(vec![(InnerDoc(" x"), 0..5)]));
        assert_eq!(lex("/*! a */"), Ok(vec![(InnerDoc(" a "), 0..8)]));
        assert_eq!(lex("/** */"),   Ok(vec![(OuterDoc(" "), 0..6)]));
        assert_eq!(lex("/*!*/"),    Ok(vec![(InnerDoc(""), 0..5)]));
    }

    #[test]
    fn lexer_literal_lifetime() {
        assert_eq!(lex("1"),            Ok(vec![(Literal("1"), 0..1)]));
        assert_eq!(lex("1isize"),       Ok(vec![(Literal("1isize"), 0..6)]));
        assert_eq!(lex("1__3_.2_8_"),   Ok(vec![(Literal("1__3_.2_8_"), 0..10)]));
        assert_eq!(lex("1.2e3f32"),     Ok(vec![(Literal("1.2e3f32"), 0..8)]));
        assert_eq!(lex("1.2e-3"),       Ok(vec![(Literal("1.2e-3"), 0..6)]));
        assert_eq!(lex("1e+3"),         Ok(vec![(Literal("1e+3"), 0..4)]));
        assert_eq!(lex("0xDeAdBeEf"),   Ok(vec![(Literal("0xDeAdBeEf"), 0..10)]));
        assert_eq!(lex("0o__1_07i8"),   Ok(vec![(Literal("0o__1_07i8"), 0..10)]));
        assert_eq!(lex("0b__1_01"),     Ok(vec![(Literal("0b__1_01"), 0..8)]));

        assert_eq!(lex("0b21"),         Err(InvalidNumberSuffix(0))); // suffix match `b21` and fails
        assert_eq!(lex("0b_1_2"),       Err(InvalidNumberSuffix(0))); // suffix match `2` and fails

        assert_eq!(lex(r#" "\"" "#),        Ok(vec![(Literal(r#""\"""#), 1..5)]));
        assert_eq!(lex(r#" b" \" \" " "#),  Ok(vec![(Literal(r#"b" \" \" ""#), 1..11)]));
        assert_eq!(lex(r#" r"\" "#),        Ok(vec![(Literal(r#"r"\""#), 1..5)]));
        assert_eq!(lex(r##" r#"\"# "##),    Ok(vec![(Literal("r#\"\\\"#"), 1..7)]));

        assert_eq!(lex(r#" "\" "#),         Err(UnterminatedString(1)));
        assert_eq!(lex(r#" br#"" "#),       Err(UnterminatedString(1)));

        assert_eq!(lex("'a'a"),             Ok(vec![(Literal("'a'"), 0..3), (Ident("a"), 3..4)]));
        assert_eq!(lex("'劲'"),             Ok(vec![(Literal("'劲'"), 0..2+"劲".len())]));
        assert_eq!(lex(r"b'\x00'"),         Ok(vec![(Literal(r"b'\x00'"), 0..7)]));
        assert_eq!(lex(r"'\''"),            Ok(vec![(Literal(r"'\''"), 0..4)]));
        assert_eq!(lex(r"'\\'"),            Ok(vec![(Literal(r"'\\'"), 0..4)]));
        assert_eq!(lex(r"'\u{99}'"),        Ok(vec![(Literal(r"'\u{99}'"), 0..8)]));
        assert_eq!(lex(r"'\u{000000}'"),    Ok(vec![(Literal(r"'\u{000000}'"), 0..12)]));

        // should be invalid
        assert_ne!(lex(r"'\u{}'"),  Ok(vec![(Literal(r"'\u{}'"), 0..6)]));
        assert_ne!(lex(r"'\x0'"),   Ok(vec![(Literal(r"'\x0'"), 0..5)]));

        assert_eq!(lex("'a 'a"),    Ok(vec![(Lifetime("a"), 0..2), (Lifetime("a"), 3..5)]));
        assert_eq!(lex("'_1a"),     Ok(vec![(Lifetime("_1a"), 0..4)]));
    }

    #[test]
    fn lexer_symbol() {
        let mut source = String::new();
        let mut expect = vec![];
        for (k, &symty) in SYMBOLS.iter() {
            expect.push((Symbol(symty), source.len()..source.len() + k.len()));
            source += k;
            source.push(' ');
        }
        println!("testing: `{}`", source);
        assert_eq!(lex(&source),    Ok(expect));
        assert_eq!(lex(">"),        Ok(vec![(Symbol(Gt), 0..1)]));
        assert_eq!(lex("> "),       Ok(vec![(Symbol(Gt), 0..1)]));
        assert_eq!(lex(">>"),       Ok(vec![(AmbigGt, 0..1), (Symbol(Gt), 1..2)]));
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
