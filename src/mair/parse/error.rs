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

/// A serious syntax error which can't be caused by incomplete code and need
/// fix immediately.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct HardSyntaxError<'a> {
    pub loc:    &'a str,
    pub reason: &'static str,
}
