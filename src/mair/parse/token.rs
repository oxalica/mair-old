use std::str::from_utf8_unchecked;
use super::ptr_diff;
use self::DelimToken::*;
use self::TokenizeError::*;
use self::Token::*;

type RawErr<'a> = TokenizeError<&'a [u8]>;

#[derive(Debug, PartialEq, Eq)]
pub enum TokenizeError<Pos=usize> {
    UnclosedComment(Pos),
    UnmatchedDelimiter(Pos, Pos),
    UnexpectedChar(Pos),
}

#[derive(Debug, PartialEq, Eq)]
pub enum DelimToken {
    Paren,
    Bracket,
    Brace,
}

#[derive(Debug, PartialEq, Eq)]
pub enum Token<'a> {
    Delimited(DelimToken, Vec<Token<'a>>),
    InnerDoc(&'a str),
    OuterDoc(&'a str),
    Ident(&'a str),
    Symbol(&'a str),
}

/// Parse source string into a list of tokens.
pub fn tokenize(source: &str) -> Result<Vec<Token>, TokenizeError> {
    let index_of = |ns: &[u8]| ptr_diff(ns.as_ptr(), source.as_ptr()) as usize;
    match tokens(source.as_bytes()) {
        Ok((tail, tts)) => if tail.is_empty() {
            Ok(tts)
        } else {
            Err(UnexpectedChar(index_of(tail)))
        },
        Err(e)          => match e {
            UnclosedComment(beg)         =>
                Err(UnclosedComment(index_of(beg))),
            UnmatchedDelimiter(beg, end) =>
                Err(UnmatchedDelimiter(index_of(beg), index_of(end))),
            UnexpectedChar(pos)          =>
                Err(UnexpectedChar(index_of(pos)))
        },
    }
}

macro_rules! match_head {
    ($s:ident; _ => $e:expr;) => ($e);
    ($s:ident; pat ($($pat:pat)|+) => $e:expr; $($tt:tt)*) => ({
        match $s[0] {
            $($pat)|+ => $e,
            _         => match_head!($s; $($tt)*),
        }
    });
    ($s:ident; $($pat:expr),+ => $e:expr; $($tt:tt)*) => ({
        if [$(&$pat[..]),+].iter().any(|p| $s.starts_with(p)) {
            $e;
        } else {
            match_head!($s; $($tt)*);
        }
    });
    ($s:ident; $($pat:expr),+; $(($c:ident))* => $e:expr; $($tt:tt)*) => ({
        if let Some(c) = [$(&$pat[..]),+].iter().find(|p| $s.starts_with(p)) {
            $(let $c = &$s[..c.len()];)*
            $s = &$s[c.len()..];
            $e;
        } else {
            match_head!($s; $($tt)*);
        }
    });
}

/// Helper parser for `tokenize`.
fn tokens(mut s: &[u8]) -> Result<(&[u8], Vec<Token>), RawErr> {
    let mut v = vec![];
    macro_rules! delimited { ($r:expr, $dm:expr) => {{
            let (mut ns, tts) = tokens(&s[1..])?;
            if trim(&mut ns) && ns[0] == $r {
                v.push(Delimited($dm, tts));
                s = &ns[1..];
            } else {
                return Err(UnmatchedDelimiter(s, ns));
            }
        }}; }
    while trim(&mut s) {
        match_head!(s;
            b")", b"]", b"}" => break;
            b"("        => delimited!(b')', Paren);
            b"["        => delimited!(b']', Bracket);
            b"{"        => delimited!(b'}', Brace);
            b"//!" ;    => v.push(InnerDoc(line_comment_inner(&mut s)));
            b"////";    => line_comment_inner(&mut s);
            b"///" ;    => v.push(OuterDoc(line_comment_inner(&mut s)));
            b"//"  ;    => line_comment_inner(&mut s);
            b"/*!" ;    => v.push(InnerDoc(block_comment_inner(&mut s)?));
            b"/***";    => block_comment_inner(&mut s)?;
            b"/**" ;    => v.push(OuterDoc(block_comment_inner(&mut s)?));
            b"/*"  ;    => block_comment_inner(&mut s)?;
            b"::", b"->", b"=>",
            b"==", b"!=", b"<=", b">=", b"<", b">",
            b"&&", b"||",
            b"!", b"=",
            b"+=", b"-=", b"*=", b"/=", b"%=",
            b"&=", b"|=", b"^=", b"<<=", b">>=",
            b"+", b"-", b"*", b"/", b"%",
            b"&", b"|", b"^", b"<<", b">>"; (c) =>
                v.push(Symbol(to_str(c)));
            pat (b'_' | b'a'...b'z' | b'A'...b'Z') => { // identifier
                let mut i = 1;
                while i < s.len() { match s[i] {
                    b'_' | b'a'...b'z' | b'A'...b'Z' | b'0'...b'9' => i += 1,
                    _ => break,
                }}
                v.push(Ident(to_str(&s[..i])));
                s = &s[i..];
            };
            _ => unimplemented!();
        );
    }
    Ok((s, v))
}

/// Parse the body of line comment(excluding '//') and return it.
#[inline]
fn line_comment_inner<'a>(s: &mut &'a [u8]) -> &'a str {
    let mut i = 0;
    while i < s.len() && !b"\r\n".contains(&s[i]) { i += 1 }
    let ret = to_str(&s[..i]);
    *s = &s[i..];
    ret
}

/// Parse the body of block comment(excluding '/*') recursively and return it.
#[inline]
fn block_comment_inner<'a>(s: &mut &'a [u8]) -> Result<&'a str, RawErr<'a>> {
    let mut ns = *s;
    let mut begins = vec![*s];
    while !begins.is_empty() { match ns.first() {
        None                                   =>
            return Err(UnclosedComment(begins.last().unwrap())),
        Some(&b'*') if s.get(1) == Some(&b'/') => {
            begins.pop();
            ns = &ns[2..];
        } ,
        Some(&b'/') if s.get(1) == Some(&b'*') => {
            begins.push(ns);
            ns = &ns[2..];
        },
        _                                      =>
            ns = &ns[1..],
    }}
    let ret = to_str(&s[..(ptr_diff(ns.as_ptr(), s.as_ptr()) as usize - 2)]);
    *s = ns;
    Ok(ret)
}

/// Remove leading spaces and return whether there's something left
#[inline]
fn trim(s: &mut &[u8]) -> bool {
    while !s.is_empty() { match s[0] {
        b' ' | 0x09...0x0D => *s = &s[1..], // b" \t\n\v\f\r"
        _ => break,
    } }
    !s.is_empty()
}

/// A shortcut to `std::str::from_utf8_unchecked`
#[inline]
fn to_str(s: &[u8]) -> &str { unsafe{ from_utf8_unchecked(s) } }

#[test]
fn test_tokenize() {
    assert_eq!(tokenize(""),                Ok(vec![]));
    assert_eq!(tokenize("  hell0 world "),  Ok(vec![Ident("hell0"), Ident("world")]));
    assert_eq!(tokenize("a"),               Ok(vec![Ident("a")]));
    assert_eq!(tokenize("()///[x\r[a]{ /*!//x{\n \t*/b0\n\t_T} "),
        Ok(vec![
            Delimited(Paren,   vec![]),
            OuterDoc("[x"),
            Delimited(Bracket, vec![Ident("a")]),
            Delimited(Brace,   vec![
                InnerDoc("//x{\n \t"),
                Ident("b0"),
                Ident("_T")
            ]),
        ])
    );
}
