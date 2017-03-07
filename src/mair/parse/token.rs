use std::str::from_utf8_unchecked;
use super::ptr_diff;
use self::DelimToken::*;
use self::TokenizeError::*;
use self::Token::*;

type Ret<'a, O> = Result<(&'a [u8], O), TokenizeError<&'a [u8]>>;

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
            _                            =>
                unreachable!(),
        },
    }
}

fn tokens(mut s: &[u8]) -> Ret<Vec<Token>> {
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
        match s[0] {
            b'(' => delimited!(b')', Paren),
            b'[' => delimited!(b']', Bracket),
            b'}' => delimited!(b'}', Brace),
            b'/' if match s.get(1) {
                Some(&b'/') => unimplemented!(),
                Some(&b'*') => unimplemented!(),
                _           => false,
            } => {},
            b'_' | b'a'...b'z' | b'A'...b'Z' => {
                let mut i = 1;
                while i < s.len() { match s[i] {
                    b'_' | b'a'...b'z' | b'A'...b'Z' | b'0'...b'9' => i += 1,
                    _ => break,
                }}
                v.push(Ident(to_str(&s[..i])));
                s = &s[i..];
            },
            _ => unimplemented!(),
        }
    }
    Ok((s, v))
}

/// Remove leading spaces and return whether there's something left
#[inline]
fn trim(s: &mut &[u8]) -> bool {
    while !s.is_empty() { match s[0] {
        b' ' | 0x09...0x0A => *s = &s[1..],
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
}
