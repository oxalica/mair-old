#![cfg_attr(feature="clippy", allow(never_loop))] // TODO: https://github.com/Manishearth/rust-clippy/issues/1586

use std::rc::Rc;
use std::collections::HashMap;
use std::char::from_u32;
use regex::{Regex, Captures, escape};
use super::{imax, fmax};
use super::ast::{Literal as Lit, Ty, Delimiter};
use super::error::{LexicalError, LexicalErrorKind};

pub type LocStr<'a> = &'a str;
pub type Token<'a> = (TokenKind<'a>, LocStr<'a>);

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum TokenKind<'input> {
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
    Literal(Lit<'input>),
    /// A delimiter.
    Delimiter{ is_open: bool, delim: Delimiter },
    /// A symbol.
    Symbol(SymbolType),
}

/// An iterator over escaped `&str` producing unescaped chars
struct EscapedChars<'a>(&'a str);

/// An iterator over `str` producing `Some(TokenKind)` for token or `None` for comment.
struct Tokenizer<'input> {
    rest: &'input str,
}

/// An iterator over `str` producing `TokenKind`.
pub struct Lexer<'input> {
    tokenizer: Tokenizer<'input>,
}

macro_rules! define_symbols(
    ($($tok:ident = $s:tt;)+) => {
        #[derive(Debug, PartialEq, Eq, Clone, Copy)]
        pub enum SymbolType {
            $($tok,)+
        }

        #[macro_export] // TODO: remove it
        macro_rules! symbol_type {
            $(($s) => ($crate::parse::lexer::SymbolType::$tok);)*
        }

        lazy_static! {
            static ref SYMBOLS: HashMap<&'static str, SymbolType> = {
                let mut m = HashMap::new();
                $(m.insert($s, SymbolType::$tok);)+
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
    ($($kw:ident = $s:tt;)+) => {
        #[derive(Debug, PartialEq, Eq, Clone, Copy)]
        pub enum KeywordType {
            $($kw,)+
        }

        #[macro_export] // TODO: remove it
        macro_rules! keyword_type {
            $(($s) => ($crate::parse::lexer::KeywordType::$kw);)*
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
    Shr         = ">>";
    AndAnd      = "&&";
    OrOr        = "||";
    EqEq        = "==";
    Ne          = "!=";
    Lt          = "<";
    Gt          = ">";
    Le          = "<=";
    Ge          = ">=";
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
    ShrEq       = ">>=";
} // define_symbols!

define_keywords! {
    // https://doc.rust-lang.org/grammar.html#keywords
    Abstract  = "abstract";
    Alignof   = "alignof";
    As        = "as";
    Become    = "become";
    Box       = "box";
    Break     = "break";
    Const     = "const";
    Continue  = "continue";
    Crate     = "crate";
    Do        = "do";
    Else      = "else";
    Enum      = "enum";
    Extern    = "extern";
    False     = "false";
    Final     = "final";
    Fn        = "fn";
    For       = "for";
    If        = "if";
    Impl      = "impl";
    In        = "in";
    Let       = "let";
    Loop      = "loop";
    Macro     = "macro";
    Match     = "match";
    Mod       = "mod";
    Move      = "move";
    Mut       = "mut";
    Offsetof  = "offsetof";
    Override  = "override";
    Priv      = "priv";
    Proc      = "proc";
    Pub       = "pub";
    Pure      = "pure";
    Ref       = "ref";
    Return    = "return";
    SelfTy    = "Self";
    SelfVar   = "self";
    Sizeof    = "sizeof";
    Static    = "static";
    Struct    = "struct";
    Super     = "super";
    Trait     = "trait";
    True      = "true";
    Type      = "type";
    Typeof    = "typeof";
    Unsafe    = "unsafe";
    Unsized   = "unsized";
    Use       = "use";
    Virtual   = "virtual";
    Where     = "where";
    While     = "while";
    Yield     = "yield";
} // define_keywords!

/// The regex match a char(maybe escaped).
const RESTR_CHAR: &'static str = r#"(?x:
    (?P<char_normal>[[:^cntrl:]&&[^\\]])|
    \\(?:
        (?P<char_escape_simple>[\\'"nrt0\n])|
        x(?P<char_escape_ascii>[[:xdigit:]]{2})|
        u\{(?P<char_escape_unicode>[[:xdigit:]]{1,6})\}
    )
)"#;

const RESTR_NUM: &'static str = r#"(?x:
    (?:
        0b(?P<num_bin>[01_]+)|
        0o(?P<num_oct>[0-7_]+)|
        0x(?P<num_hex>[[:xdigit:]]+)|
        (?P<num_body>
            \d[\d_]*
            (?P<num_float_like>
                (?:\.\d[\d_]*)?
                (?:[Ee][+-]?_*\d[_\d]*)?
            )
        )
    )
    (?P<num_suffix>\w*)
)"#;

lazy_static! {
    static ref RE_MAIN: Regex = Regex::new(&format!(r#"(?xsm)\A(?:
        (?P<line_innerdoc>//!.*?(?:\z|\n))|
        (?P<line_outerdoc>///(?:[^/].*?)??(?:\z|\n))|
        (?P<line_comment>//.*?$)|
        (?P<block_innerdoc_beg>/\*!)|
        (?P<block_outerdoc_beg_eat1>/\*\*[^*/])|
        (?P<block_comment_beg>/\*)|
        (?P<num>{num})|
        (?P<raw_string_beg>(?P<raw_string_byte>b)?r(?P<raw_string_hashes>\#*)")|
        (?P<string>
            (?P<string_byte>b)?"
            (?P<string_content>[^"\\]*(?:\\.[^"\\]*)*)
            (?P<string_closed>")?
        )|
        (?P<char>(?P<char_byte>b)?'(?P<char_content>{chr})')|
        (?P<lifetime>'[A-Za-z_]\w*)|
        (?P<delimiter>\(|\[|\{{|\}}|\]|\))|
        (?P<symbol>{symbols})|
        (?P<keyword>(?:{keywords})\b)|
        (?P<ident>[A-Za-z_]\w*)
    )"#, num=RESTR_NUM, chr=RESTR_CHAR, symbols=*RESTR_SYMBOLS, keywords=*RESTR_KEYWORDS
    )).unwrap();

    static ref RE_BLOCK_COMMENT_BEGIN_END: Regex = Regex::new(
        r"(?s).*?(?:(?P<begin>/\*)|\*/)",
    ).unwrap();

    static ref RE_NUM_SUFFIX: Regex = Regex::new(
        r"(?x)\A(?:
            (?P<int_like>[iu](?:8|16|32|64|size))|
            f(?:32|64)
        )?\z"
    ).unwrap();
}

impl<'a> EscapedChars<'a> {
    fn new(s: &'a str) -> Self {
        EscapedChars(s)
    }
}

impl<'a> Iterator for EscapedChars<'a> {
    type Item = Result<char, &'a str>;

    fn next(&mut self) -> Option<Self::Item> {
        lazy_static! {
            static ref RE_ESCAPED: Regex = Regex::new(
                &format!(r"\A{}", RESTR_CHAR)
            ).unwrap();
        }

        let err = Some(Err(self.0));

        loop {
            return if self.0.is_empty() {
                None
            } else if let Some(cap) = RE_ESCAPED.captures(self.0) {
                self.0 = &self.0[cap[0].len()..];
                Some(Ok(if let Some(s) = cap.name("char_normal") {
                    s.as_str().chars().next().unwrap()
                } else if let Some(s) = cap.name("char_escape_simple") {
                    match s.as_str().as_bytes()[0] {
                        b'n'  => '\n',
                        b'r'  => '\r',
                        b't'  => '\t',
                        b'0'  => '\0',
                        b'\n' => {
                            self.0 = self.0.trim_left();
                            continue
                        },
                        c if br#"\\'"nrt0"#.contains(&c) => c as char,
                        _     => return err,
                    }
                } else if let Some(s) = cap.name("char_escape_ascii") {
                    u8::from_str_radix(s.as_str(), 16).unwrap() as char // checked by regex
                } else if let Some(s) = cap.name("char_escape_unicode") {
                    match from_u32(u32::from_str_radix(s.as_str(), 16).unwrap()) { // ..
                        Some(c) => c,
                        None    => return err,
                    }
                } else {
                    return err
                }))
            } else { // match failed
                err
            }
        }
    }
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
    fn eat_block_comment(&mut self) -> Result<&'input str, LexicalErrorKind> {
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
                return Err(LexicalErrorKind::UnclosedComment);
            }
        }
        Ok(&sbegin[..sbegin.len() - self.rest.len() - 2]) // excluding `*/`
    }

    /// Consume raw string inner(without the starting tag) till the ending tag.
    /// Return the content of the string.
    fn eat_raw_string(&mut self, hashes: usize) -> Result<&'input str, LexicalErrorKind> {
        let pat = format!("\"{}", "#".repeat(hashes));
        if let Some(p) = self.rest.find(&pat) {
            let content = &self.rest[..p];
            self.advance(p + pat.len());
            Ok(content)
        } else {
            Err(LexicalErrorKind::UnterminatedString)
        }
    }
}

/// Parse a char-like literal captured.
fn parse_cap_char<'a>(cap: &Captures<'a>) -> Result<Lit<'a>, LexicalErrorKind> {
    let s = &cap["char_content"];
    match EscapedChars::new(s).next().unwrap() { // must have at least 1 char
        Ok(ch) if s.as_bytes()[0] != b'\'' => Ok(Lit::CharLike{ // `'''` is invalid
            is_byte: cap.name("char_byte").is_some(),
            ch,
        }),
        _ => Err(LexicalErrorKind::InvalidEscape), // TODO: save the position
    }
}

/// Parse a number-like literal captured.
fn parse_cap_num<'a>(cap: &Captures<'a>) -> Result<Lit<'a>, LexicalErrorKind> {
    use self::Lit::*;

    let err = Err(LexicalErrorKind::InvalidNumberSuffix);
    let (radix, s) = if let Some(s) = cap.name("num_bin")  { ( 2, s) }
                else if let Some(s) = cap.name("num_oct")  { ( 8, s) }
                else if let Some(s) = cap.name("num_hex")  { (16, s) }
                else if let Some(s) = cap.name("num_body") { (10, s) }
                else { unreachable!() };
    let s = s.as_str().replace("_", "");
    let mut lit = if cap.name("num_float_like").map_or(false, |s| !s.as_str().is_empty()) {
        FloatLike{ ty: None, val: s.parse().unwrap() } // checked by regex
    } else {
        IntLike{ ty: None, val: imax::from_str_radix(&s, radix).unwrap() } // ..
    };
    if let Some(cap_suf) = RE_NUM_SUFFIX.captures(cap.name("num_suffix").unwrap().as_str()) {
        if !cap_suf[0].is_empty() {
            let ty_suf = Ty::from_name(cap_suf.get(0).unwrap().as_str());
            if cap_suf.name("int_like").is_some() {
                match lit {
                    IntLike{ ref mut ty, .. }   =>
                        *ty = Some(Box::new(ty_suf)),
                    FloatLike{..}               => return err,
                    _                           => unreachable!(),
                }
            } else { // float-like
                match lit {
                    IntLike{ val, .. }          => lit = FloatLike {
                        ty: Some(Box::new(ty_suf)),
                        val: val as fmax,
                    },
                    FloatLike{ ref mut ty, .. } =>
                        *ty = Some(Box::new(ty_suf)),
                    _                           => unreachable!(),
                }
            }
        }
        Ok(lit)
    } else { // unmatched suffix
        err
    }
}

/// Parse a string-like literal.
fn parse_str_string(source: &str, is_bytestr: bool, is_raw: bool)
        -> Result<Lit, LexicalErrorKind> {
    let mut s;
    if is_raw {
        s = String::from(source)
    } else {
        s = String::new();
        for ret in EscapedChars::new(source) {
            match ret {
                Ok(c)  => s.push(c),
                Err(_) => Err(LexicalErrorKind::InvalidEscape)?, // TODO: save the position
            }
        }
    };
    Ok(Lit::StrLike{ is_bytestr, s: Rc::new(s) })
}

impl<'input> Iterator for Tokenizer<'input> {
    type Item =
        Result<Option<(TokenKind<'input>, &'input str)>, LexicalError<'input>>;

    fn next(&mut self) -> Option<Self::Item> {
        use self::TokenKind::*;
        use self::LexicalErrorKind::*;

        let slast = self.rest.trim_left();
        self.rest = slast;
        if self.rest.is_empty() {
            None
        } else if let Some(cap) = RE_MAIN.captures(self.rest) {
            self.advance(cap[0].len());
            let is = |name| cap.name(name).is_some();
            let mut f = || -> Result<_, LexicalErrorKind> {
                // wrap for the carriers inside
                Ok(match cap.get(0).unwrap().as_str() {
                    m if is("line_innerdoc")        => Some(InnerDoc(&m[3..])),
                    m if is("line_outerdoc")        => Some(OuterDoc(&m[3..])),
                    _ if is("line_comment")         => None,
                    m if is("lifetime")             => Some(Lifetime(&m[1..])),
                    m if is("keyword")              => if m == "true" {
                        Some(Literal(Lit::Bool(true)))
                    } else if m == "false" {
                        Some(Literal(Lit::Bool(false)))
                    } else {
                        Some(Keyword(KEYWORDS[m]))
                    },
                    m if is("ident")                => Some(Ident(m)),
                    _ if is("block_innerdoc_beg")   => Some(InnerDoc(self.eat_block_comment()?)),
                    _ if is("char")                 => Some(Literal(parse_cap_char(&cap)?)),
                    _ if is("num")                  => Some(Literal(parse_cap_num(&cap)?)),
                    m if is("symbol")               => Some(Symbol(SYMBOLS[m])),
                    _ if is("string")               => {
                        if !is("string_closed") {
                            Err(UnterminatedString)?
                        } else {
                            let content = cap.name("string_content").unwrap().as_str();
                            Some(Literal(parse_str_string(content, is("string_byte"), false)?))
                        }
                    },
                    _ if is("raw_string_beg")       => {
                        let s = self.eat_raw_string(cap["raw_string_hashes"].len())?;
                        Some(Literal(parse_str_string(s, is("raw_string_byte"), true)?))
                    },
                    _ if is("block_outerdoc_beg_eat1")  => {
                        self.rest = &slast[cap[0].len() - 1..]; // put the eaten first char back
                        Some(OuterDoc(self.eat_block_comment()?))
                    },
                    _ if is("block_comment_beg")    => {
                        self.eat_block_comment()?;
                        None
                    },
                    m if is("delimiter")            => {
                        use self::Delimiter::*;
                        let is_open = match m {
                            "(" | "[" | "{" => true,
                            _               => false,
                        };
                        let delim = match m {
                            "(" | ")" => Paren,
                            "[" | "]" => Bracket,
                            _         => Brace,
                        };
                        Some(Delimiter{ is_open, delim })
                    },
                    _ => unreachable!(),
                })
            };
            match f() {
                Ok(None)        => Some(Ok(None)),
                Ok(Some(tokty)) => Some(Ok(Some((tokty, &slast[..slast.len() - self.rest.len()])))),
                Err(e)          => Some(Err(LexicalError{ loc: slast, kind: e })),
            }
        } else { // regex match fails
            Some(Err(LexicalError{ loc: self.rest, kind: UnknowToken}))
        }
    }
}

impl<'input> Lexer<'input> {
    pub fn new(input: &'input str) -> Self {
        Lexer{ tokenizer: Tokenizer::new(input) }
    }
}

impl<'input> Iterator for Lexer<'input> {
    type Item = Result<Token<'input>, LexicalError<'input>>;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            return match self.tokenizer.next() {
                None                                 => None,
                Some(Ok(None))                       => continue, // skip comment as space
                Some(Ok(Some((tokty, s))))           => Some(Ok((tokty, s))),
                Some(Err(LexicalError{ loc, kind })) =>
                    Some(Err(LexicalError{ loc, kind })),
            }
        }
    }
}
