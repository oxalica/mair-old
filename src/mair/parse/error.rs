use super::lexer::Loc;

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
}

/// The only error may be thrown by `parse::grammar::TTParser::next()`.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct UnmatchedDelimError(pub Loc);
