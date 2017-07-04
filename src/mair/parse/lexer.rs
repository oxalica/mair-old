#![cfg_attr(feature="clippy", allow(never_loop))] // TODO: https://github.com/Manishearth/rust-clippy/issues/1586

use std::ops::Range;
use std::iter::Peekable;
use std::collections::HashMap;
use std::char::from_u32;
use regex::{Regex, Captures, escape};
use super::{imax, fmax, str_ptr_diff};
use super::ast::{Literal as Lit, Ty, PluginInvoke, Delimiter};

pub type Pos = usize;
pub type Loc = Range<Pos>;

#[derive(Debug, PartialEq, Eq, Clone)]
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
    Literal(Lit<'input>),
    /// A symbol.
    Symbol(LexSymbol),
    /// The ambiguous symbol `>` followed by `>` or `=`. eg. `>>` will be parsed into
    /// an `AmbigGt` and a normal `Symbol`, for that the first `>` can be either the end of
    /// template or a bitwise right shift operator when combining the following `>`.
    AmbigGt,
    /// A plugin(including macro) invocation using delimiter `{}` (Item-like).
    PluginInvokeItem(PluginInvoke<'input>),
    /// A plugin(including macro) invocation using delimiter `()` or `[]` (Expression-like).
    PluginInvokeExpr(PluginInvoke<'input>),
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct LexicalError<P> {
    pub pos:  P,
    pub kind: LexicalErrorKind,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum LexicalErrorKind {
    UnknowToken,
    UnclosedComment,
    UnterminatedString,
    InvalidNumberSuffix,
    InvalidEscape,
    InvalidPluginInvoke,
    UnmatchedPluginInvokeDelim,
}

/// An iterator over escaped `&str` producing unescaped chars
struct EscapedChars<'a>(&'a str);

/// An iterator over `str` producing `Some(LexToken)` for token or `None` for comment.
struct Tokenizer<'input> {
    rest: &'input str,
}

/// An basic iterator,
struct RawLexer<'input> {
    source: &'input str,
    tokenizer: Tokenizer<'input>,
}

/// An iterator over `str` whose output is compatible with the lalrpop parser.
/// It will process plugin invocations.
pub struct Lexer<'input>(Peekable<RawLexer<'input>>);

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
                (?:[Ee][+-]?[\d_]+)?
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
                    IntLike{ ref mut ty, .. }   => *ty = Some(ty_suf),
                    FloatLike{..}               => return err,
                    _                           => unreachable!(),
                }
            } else { // float-like
                match lit {
                    IntLike{ val, .. }          => lit = FloatLike {
                        ty: Some(ty_suf),
                        val: val as fmax,
                    },
                    FloatLike{ ref mut ty, .. } => *ty = Some(ty_suf),
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
    Ok(Lit::StrLike{ is_bytestr, s })
}

impl<'input> Iterator for Tokenizer<'input> {
    type Item = Result<Option<(LexToken<'input>, &'input str)>, LexicalError<&'input str>>;

    fn next(&mut self) -> Option<Self::Item> {
        use self::LexToken::*;
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
                    m if is("keyword")              => Some(Keyword(KEYWORDS[m])),
                    m if is("ident")                => Some(Ident(m)),
                    _ if is("block_innerdoc_beg")   => Some(InnerDoc(self.eat_block_comment()?)),
                    _ if is("char")                 => Some(Literal(parse_cap_char(&cap)?)),
                    _ if is("num")                  => Some(Literal(parse_cap_num(&cap)?)),
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
                Err(e)          => Some(Err(LexicalError{ pos: slast, kind: e })),
            }
        } else { // regex match fails
            Some(Err(LexicalError{ pos: self.rest, kind: UnknowToken}))
        }
    }
}

impl<'input> RawLexer<'input> {
    pub fn new(input: &'input str) -> Self {
        RawLexer{ source: input, tokenizer: Tokenizer::new(input) }
    }

    /// Get the start and end index of a subslice of `source`.
    /// Panic if `s` is not a subslice of `source`.
    fn pos(&self, s: &'input str) -> (usize, usize) {
        let p = str_ptr_diff(s, self.source);
        assert!(0 <= p && p as usize <= self.source.len());
        (p as usize, p as usize + s.len())
    }
}

impl<'input> Iterator for RawLexer<'input> {
    type Item = Result<(Pos, LexToken<'input>, Pos), LexicalError<usize>>;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            return match self.tokenizer.next() {
                None                                 => None,
                Some(Ok(None))                       => continue, // skip comment as space
                Some(Ok(Some((tokty, s))))           => {
                    let (beg, end) = self.pos(s);
                    Some(Ok((beg, tokty, end)))
                },
                Some(Err(LexicalError{ pos, kind })) =>
                    Some(Err(LexicalError{ pos: self.pos(pos).0, kind })),
            }
        }
    }
}

impl<'input> Lexer<'input> {
    pub fn new(input: &'input str) -> Self {
        Lexer(RawLexer::new(input).peekable())
    }

    /// Process the plugin arguments, which are an optional identifier and a block.
    /// `name` is the plugin name to invoke. `begin_pos` is for the InvalidPluginInvoke error.
    fn plugin_invoke_args(&mut self, name: &'input str, begin_pos: usize)
            -> Result<(Pos, PluginInvoke<'input>, Pos), LexicalError<usize>> {
        use self::LexicalErrorKind::*;
        use self::LexSymbol::*;
        use self::Delimiter::*;

        let lex = &mut self.0;
        let err_invoke = Err(LexicalError{ pos: begin_pos, kind: InvalidPluginInvoke });
        let err_unmatch = |pos| Err(LexicalError{ pos, kind: UnmatchedPluginInvokeDelim });
        let delim_ty = |sym| match sym {
            LParen | RParen     => Paren,
            LBracket | RBracket => Bracket,
            LBrace | RBrace     => Brace,
            _                   => unreachable!(),
        };
        let ident = match lex.peek() {
            Some(&Ok((_, LexToken::Ident(c), _))) => { lex.next(); Some(c) },
            _                                     => None,
        };
        let delim;
        let mut delims = vec![];
        match lex.next() {
            Some(Ok((l, LexToken::Symbol(sym), _))) => match sym {
                LParen | LBracket | LBrace => { delim = delim_ty(sym); delims.push((l, delim)) },
                _                          => return err_invoke,
            },
            Some(Err(e)) => return Err(e),
            _            => return err_invoke,
        }
        let mut tts = vec![];
        let end_pos;
        loop {
            match lex.next() {
                Some(Ok((l, LexToken::Symbol(sym), r))) => {
                    match sym {
                        LParen | LBracket | LBrace => delims.push((l, delim_ty(sym))),
                        RParen | RBracket | RBrace => match delims.pop() {
                            None              => return err_unmatch(l),
                            Some((_, expect)) => if expect != delim_ty(sym) {
                                return err_unmatch(l);
                            } else if delims.is_empty() {
                                end_pos = r;
                                break;
                            },
                        },
                        _                          => (),
                    }
                    tts.push((LexToken::Symbol(sym), l..r));
                },
                Some(Ok((l, tok, r))) => tts.push((tok, l..r)),
                Some(Err(e))          => return Err(e),
                None                  => return err_unmatch(delims.last().unwrap().0),
            }
        }
        Ok((begin_pos, PluginInvoke{ name, delim, ident, tts }, end_pos))
    }
}

impl<'input> Iterator for Lexer<'input> {
    type Item = Result<(Pos, LexToken<'input>, Pos), LexicalError<usize>>;

    fn next(&mut self) -> Option<Self::Item> {
        use self::LexToken::*;

        match (self.0.next(), self.0.peek()) {
            (Some(Ok((l, Ident(name), _))), Some(&Ok((_, Symbol(LexSymbol::Bang), _)))) => {
                self.0.next(); // eat `!`
                match self.plugin_invoke_args(name, l) {
                    Err(e)          => Some(Err(e)),
                    Ok((l, inv, r)) => Some(Ok(if inv.delim == Delimiter::Brace {
                        (l, PluginInvokeItem(inv), r)
                    } else {
                        (l, PluginInvokeExpr(inv), r)
                    })),
                }
            },
            (c, _) => c,
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use super::LexToken::*;
    use super::KeywordType::*;
    use super::LexSymbol::*;
    use super::LexicalErrorKind::*;

    fn lex(input: &str) -> Result<Vec<(LexToken, Loc)>, LexicalError<usize>> {
        let mut v = vec![];
        for c in Lexer::new(input) {
            let (l, tok, r) = c?;
            v.push((tok, l..r));
        }
        Ok(v)
    }

    fn unesc(input: &str) -> Result<String, &str> {
        let mut s = String::new();
        for ret in EscapedChars::new(input) {
            s.push(ret?);
        }
        Ok(s)
    }

    #[test]
    fn unescape_chars() {
        let s = |s| String::from(s);

        assert_eq!(unesc(""),                   Ok(s("")));
        assert_eq!(unesc("\"x'"),               Ok(s("\"x'")));
        assert_eq!(unesc("abc呢"),              Ok(s("abc呢")));
        assert_eq!(unesc("\x7aa"),              Ok(s("\x7Aa")));
        assert_eq!(unesc(r"\u{1}"),             Ok(s("\x01")));
        assert_eq!(unesc(r"\u{2764}"),          Ok(s("\u{2764}")));
        assert_eq!(unesc("\\\n\r a"),           Ok(s("a")));
        assert_eq!(unesc(r#"\\\'\"\n\r\t\0"#),  Ok(s("\\\'\"\n\r\t\0")));

        assert_eq!(unesc(r"aa\u{}"),            Err(r"\u{}"));
        assert_eq!(unesc(r"\a"),                Err(r"\a"));
        assert_eq!(unesc(r"\x0"),               Err(r"\x0"));
        assert_eq!(unesc(r"\x0*"),              Err(r"\x0*"));
        assert_eq!(unesc(r"\u{999999}"),        Err(r"\u{999999}"));
    }

    #[test]
    fn lexer_plugin_invoke() {
        use self::Delimiter::*;

        let ok_expr = |p: Loc, name, delim, ident, tts|
            Ok(vec![(PluginInvokeExpr(PluginInvoke{ name, delim, ident, tts }), p)]);
        let ok_item = |p: Loc, name, delim, ident, tts|
            Ok(vec![(PluginInvokeItem(PluginInvoke{ name, delim, ident, tts }), p)]);
        assert_eq!(lex("a!()"),  ok_expr(0..4, "a", Paren,   None, vec![] ));
        assert_eq!(lex("a![]"),  ok_expr(0..4, "a", Bracket, None, vec![] ));
        assert_eq!(lex("a!{}"),  ok_item(0..4, "a", Brace,   None, vec![] ));
        assert_eq!(lex("a!a{}"), ok_item(0..5, "a", Brace,   Some("a"), vec![] ));

        let ok2 = |p, v| ok_item(p, "a", Brace, None, v);
        assert_eq!(lex("a!{a}"), ok2(0..5, vec![(Ident("a"), 3..4)] ));
        assert_eq!(lex("a!{a[]}"), ok2(0..7, vec![
            (Ident("a"), 3..4), (Symbol(LBracket), 4..5), (Symbol(RBracket), 5..6)
        ]));
        assert_eq!(lex("a!{a[b(c)d{e}f]}"), ok2(0..16, vec![
            (Ident("a"), 3..4),   (Symbol(LBracket), 4..5),
            (Ident("b"), 5..6),   (Symbol(LParen),   6..7),
            (Ident("c"), 7..8),   (Symbol(RParen),   8..9),
            (Ident("d"), 9..10),  (Symbol(LBrace),   10..11),
            (Ident("e"), 11..12), (Symbol(RBrace),   12..13),
            (Ident("f"), 13..14), (Symbol(RBracket), 14..15),
        ]));

        assert_eq!(lex("a!"),  Err(LexicalError{ pos: 0, kind: InvalidPluginInvoke }));
        assert_eq!(lex("a!b"), Err(LexicalError{ pos: 0, kind: InvalidPluginInvoke }));
        assert_eq!(lex("a!("), Err(LexicalError{ pos: 2, kind: UnmatchedPluginInvokeDelim }));
        assert_eq!(lex("a!a[)"), Err(LexicalError{ pos: 4, kind: UnmatchedPluginInvokeDelim }));
    }

    #[test]
    fn lexer_keyword_ident() {
        assert_eq!(lex("_"),        Ok(vec![(Ident("_"), 0..1)]));
        assert_eq!(lex("a"),        Ok(vec![(Ident("a"), 0..1)]));
        assert_eq!(lex("as"),       Ok(vec![(Keyword(KwAs), 0..2)]));
        assert_eq!(lex("asc"),      Ok(vec![(Ident("asc"), 0..3)]));
        assert_eq!(lex("a0__c_"),   Ok(vec![(Ident("a0__c_"), 0..6)]));
        assert_eq!(lex("_9 a0"),    Ok(vec![(Ident("_9"), 0..2), (Ident("a0"), 3..5)]));
        assert_eq!(lex("macro_rules"), Ok(vec![(Ident("macro_rules"), 0..11)]));
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

        assert_eq!(lex(" /*"),                              Err(LexicalError{ pos: 1, kind: UnclosedComment }));
        assert_eq!(lex("/*/**/*//**"),                      Err(LexicalError{ pos: 8, kind: UnclosedComment }));
        assert_eq!(lex("/*/*! */"),                         Err(LexicalError{ pos: 0, kind: UnclosedComment }));
        assert_eq!(lex(r#"a/*0/**/"/*'/*//*/+*/#*/ a"#),    Err(LexicalError{ pos: 1, kind: UnclosedComment }));

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
        let styi32 = Some(Ty::from_name("i32"));
        let styf64 = Some(Ty::from_name("f64"));

        assert_eq!(lex("1"),            Ok(vec![(Literal(Lit::IntLike{ ty: None, val: 1 }), 0..1)]));
        assert_eq!(lex("1i32"),         Ok(vec![(Literal(Lit::IntLike{ ty: styi32.clone(), val: 1 }), 0..4)]));
        assert_eq!(lex("1__3_.2_8_"),   Ok(vec![(Literal(Lit::FloatLike{ ty: None, val: 13.28 }), 0..10)]));
        assert_eq!(lex("1.2e3f64"),     Ok(vec![(Literal(Lit::FloatLike{ ty: styf64.clone(), val: 1.2e3 }), 0..8)]));
        assert_eq!(lex("1.2e-3"),       Ok(vec![(Literal(Lit::FloatLike{ ty: None, val: 1.2e-3 }), 0..6)]));
        assert_eq!(lex("1e+3"),         Ok(vec![(Literal(Lit::FloatLike{ ty: None, val: 1e3 }), 0..4)]));
        assert_eq!(lex("0xDeAdBeEf64"), Ok(vec![(Literal(Lit::IntLike{ ty: None, val: 0xDEADBEEF64 }), 0..12)]));
        assert_eq!(lex("0o__1_07f64"),  Ok(vec![(Literal(Lit::FloatLike{ ty: styf64.clone(), val: 0o107i32 as f64 }), 0..11)])); // TODO
        assert_eq!(lex("0b__1_01"),     Ok(vec![(Literal(Lit::IntLike{ ty: None, val: 0b101 }), 0..8)]));

        assert_eq!(lex("0b21"),         Err(LexicalError{ pos: 0, kind: InvalidNumberSuffix })); // suffix match `b21` and fails
        assert_eq!(lex("0b_1_2"),       Err(LexicalError{ pos: 0, kind: InvalidNumberSuffix })); // suffix match `2` and fails

        let lstr = |is_bytestr, s| Literal(Lit::StrLike{ is_bytestr, s: String::from(s) });
        assert_eq!(lex(r#" "\"" "#),        Ok(vec![(lstr(false, "\""), 1..5)]));
        assert_eq!(lex(r#" b" \" \" " "#),  Ok(vec![(lstr(true, " \" \" "), 1..11)]));
        assert_eq!(lex(r#" r"\" "#),        Ok(vec![(lstr(false, "\\"), 1..5)]));
        assert_eq!(lex(r##" r#"\"# "##),    Ok(vec![(lstr(false, "\\"), 1..7)]));

        assert_eq!(lex(r#" "\" "#),         Err(LexicalError{ pos: 1, kind: UnterminatedString }));
        assert_eq!(lex(r#" br#"" "#),       Err(LexicalError{ pos: 1, kind: UnterminatedString }));

        let chr = |is_byte, ch| Literal(Lit::CharLike{ is_byte, ch });
        assert_eq!(lex("'a'a"),             Ok(vec![(chr(false, 'a'), 0..3), (Ident("a"), 3..4)]));
        assert_eq!(lex("'劲'"),             Ok(vec![(chr(false, '劲'), 0..2+"劲".len())]));
        assert_eq!(lex(r"b'\x00'"),         Ok(vec![(chr(true, '\0'), 0..7)]));
        assert_eq!(lex(r"'\''"),            Ok(vec![(chr(false, '\''), 0..4)]));
        assert_eq!(lex(r"'\\'"),            Ok(vec![(chr(false, '\\'), 0..4)]));
        assert_eq!(lex(r"'\u{99}'"),        Ok(vec![(chr(false, '\u{99}'), 0..8)]));
        assert_eq!(lex(r"'\u{000000}'"),    Ok(vec![(chr(false, '\0'), 0..12)]));

        // should be invalid
        assert_eq!(lex(r#""\u{}""#), Err(LexicalError{ pos: 0, kind: InvalidEscape }));
        assert!(lex(r"'\x0'").is_err());

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
        let ret = lex(&source);
        println!("{:?}", ret);
        assert!(ret.is_ok());
    }
}
