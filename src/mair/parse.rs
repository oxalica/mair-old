use std::iter::{Iterator, Peekable};
use std::ops::Range;

pub type Scope = Range<usize>;
pub type IndexedChar = (usize, char);
pub type Token = (Scope, TokenType);
pub struct RemoveComment<'a, T>(Peekable<T>, &'a mut Vec<ParseError>) where
    T: Iterator<Item=IndexedChar>;
pub struct Tokenize<'a, T>(T, &'a mut Vec<ParseError>) where
    T: Iterator<Item=IndexedChar>;

#[derive(Debug, PartialEq)]
pub enum ParseError {
    UnclosedComment(usize),
    UnclosedStringLit(usize),
    InvalidEscapedChar(usize),
    InvalidCharLit(usize),
}

#[derive(Debug)]
pub enum TokenType {
    Ident,
    Symbol,
    Literal(LitType),
}

#[derive(Debug)]
pub enum LitType {
    Char,
    Byte,
    String,
    ByteString,
    Int,
    Float,
    Bool,
    Suffixed(Scope),
}

impl<'a, T> Iterator for RemoveComment<'a, T> where
    T: Iterator<Item=IndexedChar> {
    type Item = IndexedChar;
    fn next(&mut self) -> Option<Self::Item> {
        let s = &mut self.0;
        match (s.next(), s.peek()) {
            (Some((i, '/')), Some(&(_, '/'))) => { // line comment
                while s.next().map_or(false, |(_, c)| c != '\n') {}
                Some((i, ' '))
            },
            (Some((i, '/')), Some(&(_, '*'))) => { // block comment
                s.next(); // eat char for that `/*/` is illegal
                let mut begins = vec![i];
                while !begins.is_empty() {
                    match (s.next(), s.peek()) {
                        (Some((i, '/')), Some(&(_, '*'))) => {
                            s.next(); // eat
                            begins.push(i);
                        }
                        (Some((_, '*')), Some(&(_, '/'))) => {
                            s.next(); // eat
                            begins.pop();
                        }
                        (None, _) => {
                            for pos in begins {
                                self.1.push(ParseError::UnclosedComment(pos));
                            }
                            break
                        },
                        _ => {},
                    }
                }
                Some((i, ' '))
            },
            (ret, _) => ret,
        }
    }
}

impl<'a, T> Iterator for Tokenize<'a, T> where
    T: Iterator<Item=IndexedChar> {
    type Item = Token;
    fn next(&mut self) -> Option<Self::Item> {
        unimplemented!()
    }
}

#[test]
fn remove_comment() {
    let f = |si: &str, so: &str, v: &[usize]| {
        let mut errs = vec![];
        let ret = RemoveComment(si.char_indices().peekable(), &mut errs)
            .map(|(_, c)| c)
            .collect::<String>();
        let v = v.into_iter()
            .map(|&x| ParseError::UnclosedComment(x))
            .collect::<Vec<_>>();
        assert_eq!((&ret as &str, errs), (so, v));
    };
    f("",                 "",               &[]);
    f("a/\n/ *de*f/g",    "a/\n/ *de*f/g",  &[]);
    f("a/b/*/de*/fg",     "a/b fg",         &[]);
    f("a/b//*/d\nd*/dd",  "a/b d*/dd",      &[]);
    f("abc//",            "abc ",           &[]);
    f("abc/* /*not*/in",  "abc ",           &[3]);
    f("a/*/*/*/c*/*/*/d", "a d",            &[]);
    f("a/*/*/*/*/*/*/d",  "a ",             &[1, 3, 5, 7, 9, 11]);
}
