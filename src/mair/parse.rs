use std::iter::{Iterator, Peekable};
use std::ops::Range;

pub type Scope = Range<usize>;
pub type IndexedChar = (usize, char);
pub type Token = (Scope, TokenType);
pub struct RemoveComment<T: Iterator<Item=IndexedChar>>(Peekable<T>);
pub struct Tokenize<T: Iterator<Item=IndexedChar>>(T);

pub enum TokenType {
    Ident,
    Symbol,
    Literal(LitType),
}

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

impl<T: Iterator<Item=IndexedChar>> Iterator for RemoveComment<T> {
    type Item = IndexedChar;
    fn next(&mut self) -> Option<Self::Item> {
        let s = &mut self.0;
        return match (s.next(), s.peek()) {
            (Some((i, '/')), Some(&(_, '/'))) => { // line comment
                while s.next().map_or(false, |(_, c)| c != '\n') {}
                Some((i, ' '))
            },
            (Some((i, '/')), Some(&(_, '*'))) => { // block comment
                s.next(); // eat char for that `/*/` is illegal
                let mut layer = 1usize;
                while layer > 0 {
                    match (s.next(), s.peek()) {
                        (Some((_, '/')), Some(&(_, '*'))) => {
                            s.next(); // eat
                            layer = layer + 1
                        }
                        (Some((_, '*')), Some(&(_, '/'))) => {
                            s.next(); // eat
                            layer = layer - 1
                        }
                        (None, _) => { layer = 0 }, // break if unclosed
                        _ => {},
                    }
                }
                Some((i, ' '))
            },
            (ret, _) => ret,
        }
    }
}

impl<T: Iterator<Item=IndexedChar>> Iterator for Tokenize<T> {
    type Item = Token;
    fn next(&mut self) -> Option<Self::Item> {
        unimplemented!()
    }
}

#[test]
fn remove_comment() {
    let f = |si: &str, so: &str| assert_eq!(
        RemoveComment(si.char_indices().peekable())
            .map(|(_, c)| c)
            .collect::<String>(),
        so.to_owned());
    f("", "");
    f("a/\n/ *de*f/g", "a/\n/ *de*f/g");
    f("a/b/*/de*/fg", "a/b fg");
    f("a/b//*/d\nd*/dd", "a/b d*/dd");
    f("abc//", "abc ");
    f("abc/* /*not*/in", "abc ");
    f("a/*/*/*/c*/*/*/d", "a d");
    f("a/*/*/*/*/*/*/d", "a ");
}
