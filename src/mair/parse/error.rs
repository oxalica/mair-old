use super::ast::LocStr;

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct LexicalError<'a> {
    pub loc:  LocStr<'a>,
    pub kind: LexicalErrorKind,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum LexicalErrorKind {
    UnknowToken,
    UnclosedComment,
    UnterminatedString,
    InvalidNumberSuffix,
    InvalidEscape,
}

/// The only error may be thrown by `parse::grammar::TTParser::next()`.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct UnmatchedDelimError<'a>(pub LocStr<'a>);
