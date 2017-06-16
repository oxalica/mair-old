use std::cmp::Eq;
use super::lexer::KeywordType;
use super::{imax, fmax};

/// A module, or a crate, as well as a rust source file.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Mod<'a> {
    pub attrs:        Vec<Attr<'a>>,
    pub extern_crate: Vec<&'a str>,
    pub items:        Vec<Item<'a>>,
}

/// An Item, which is the component of a crate/module.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Item<'a> {
    pub attrs:  Vec<Attr<'a>>,
    pub is_pub: bool,
    pub detail: ItemDetail<'a>,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum ItemDetail<'a> {
    Mod   (Box<Mod<'a>>),
    Use   (UseDetail<'a>),
    Func  (Template<'a>, FuncTy<'a>),
    Type  (Template<'a>, &'a str, Ty<'a>),
    Struct(Template<'a>, &'a str, StructDetail<'a>),
    Enum  (Template<'a>, &'a str, Vec<ElemField<'a>>),
    Const (&'a str, Ty<'a>, Expr<'a>),
    Static(&'a str, Ty<'a>, Expr<'a>),
    Trait (Template<'a>, &'a str, Vec<TraitItem<'a>>),
    Impl  (Template<'a>, &'a str, Option<Ty<'a>>, Vec<ImplItem<'a>>),
}

/// The item or variable referred in a `use` declaration.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum UseDetail<'a> {
    /// Bind everything under a path, like `std::str::*`.
    UseAll(Path<'a>),
    /// Bind one item or variable as new name, like `std::Option as Maybe`.
    UseAs (Path<'a>, &'a str),
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum ElemField<'a> {
    Tuple (Vec<Attr<'a>>, &'a str, Vec<Ty<'a>>),
    Struct(Vec<Attr<'a>>, &'a str, Vec<(Vec<Attr<'a>>, Ty<'a>)>),
}

/// Struct content.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum StructDetail<'a> {
    /// Unit struct, like `struct T;`.
    Unit,
    /// Tuple struct, like `struct T(i32, i32);`.
    Tuple (Vec<StructTupleElem<'a>>),
    /// Normal struct with fields, like `struct T{ a: i32, };`.
    Fields(Vec<StructField<'a>>),
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct StructTupleElem<'a> {
    pub attrs:  Vec<Attr<'a>>,
    pub is_pub: bool,
    pub ty:     Ty<'a>,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct StructField<'a> {
    pub attrs:  Vec<Attr<'a>>,
    pub is_pub: bool,
    pub name:   &'a str,
    pub ty:     Ty<'a>,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum TraitItem<'a> {
    Type(Vec<Attr<'a>>, &'a str, Ty<'a>),
    Func(Vec<Attr<'a>>, Template<'a>, FuncTy<'a>, Option<FuncBody<'a>>),
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum ImplItem<'a> {
    Type(Vec<Attr<'a>>, &'a str, Ty<'a>),
    Func(Vec<Attr<'a>>, Template<'a>, FuncTy<'a>, FuncBody<'a>),
}

/// A path, like `::std::Option`, `MyEnum::A`, etc.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Path<'a> {
    /// An absolute path like `::std::i32`.
    Absolute(Vec<PathComp<'a>>),
    /// An relative path like `i32` or `super::SomeStruct`.
    Relative{ supers: usize, tails: Vec<PathComp<'a>> },
    /// An path which begins with a type in a pair of angle brackets,
    /// like `<i32>::min_value` or `<::std::option::Option<i32>>::is_none`.
    Ty{ ty: Box<Ty<'a>>, tails: Vec<PathComp<'a>> },
}

/// A path component, maybe with template hint (if any).
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct PathComp<'a> {
    pub body: &'a str,
    pub hint: Option<Vec<Ty<'a>>>,
}

/// Template types and trait bounds.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Template<'a> {
    pub lifetimes:    Vec<&'a str>,
    pub tys:          Vec<&'a str>,
    pub trait_bounds: Vec<(Ty<'a>, Trait<'a>)>,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Trait<'a> {
    pub name:      &'a str,
    pub lifetimes: Vec<&'a str>,
    pub params:    Vec<Ty<'a>>,
}

/// A type.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Ty<'a> {
    /// The placeholder `_`.
    Hole,
    /// A generic type applied with type paramaters, like `Vec<i32>`.
    /// No paramaters indicates a normal type, like `i32`.
    Apply(Path<'a>, Vec<Ty<'a>>),
    /// A tuple type, like `(i32, i64)`.
    Tuple(Vec<Ty<'a>>),
    /// A function pointer, like `fn(i32, u8) -> usize`.
    Func(FuncTy<'a>),
    /// Trait object.
    Trait(Trait<'a>),
    /// Reference.
    Ref{ is_mut: bool, lifetime: &'a str, inner: Box<Ty<'a>> },
    /// Pointers.
    Ptr{ is_mut: bool, inner: Box<Ty<'a>> },
}

/// The type of function.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum FuncTy<'a> {
    /// Diverging function, like `fn() -> !`
    Diverging(Vec<Ty<'a>>),
    /// Other normal function, like `fn(i32) -> i32`.
    Normal(Vec<Ty<'a>>, Box<Ty<'a>>),
}

/// An attribute.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Attr<'a> {
    /// A single attribute name, like `test`, `macro_use`.
    Flag(&'a str),
    /// A key-value pair, like `crate_type = "lib"`, `recursion_limit="64"`.
    Value{ key: &'a str, value: Literal<'a> },
    /// An attribute with a list of sub-attribute arguments,
    /// like `cfg(target_os="linux")`.
    Sub(&'a str, Vec<Attr<'a>>),
}

pub type FuncBody<'a> = Vec<Token<'a>>;
pub type Expr<'a> = Vec<Token<'a>>;

/// A token or the root of a token tree.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Token<'a> {
    /// A token tree delimited with `()`, `[]` or `{}`.
    Delimited(Delimiter, Vec<Token<'a>>),
    /// An inner document.
    InnerDoc(&'a str),
    /// An outer document.
    OuterDoc(&'a str),
    /// An keyword.
    Keyword(KeywordType),
    /// An identifier or `_`.
    Ident(&'a str),
    /// A lifetime.
    Lifetime(&'a str),
    /// A symbol(can't be a delimiter), always the longest. For example, `>>` will be always
    /// parsed into a single `Symbol` rather than 2 `>`s, even though it's a part of template.
    Symbol(&'static str),
    /// A literal.
    Literal(Literal<'a>),
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum Delimiter {
    /// `()`
    Paren,
    /// `[]`
    Bracket,
    /// `{}`
    Brace,
}


#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum OperatorType {
    // https://doc.rust-lang.org/grammar.html#unary-operator-expressions
    Neg, Deref, Not,

    // https://doc.rust-lang.org/grammar.html#binary-operator-expressions
    Plus, Sub, Mul, Div, Mod,
    And, Or, Xor, Shl, Shr,
    LogAnd, LogOr,
    Equ, Ne, Lt, Gt, Le, Ge,
    As,
    Assign,
    AddAssign, SubAssign, MulAssign, DivAssign, ModAssign,
    AndAssign, OrAssign, XorAssign, ShlAssign, ShrAssign,
}

/// A literal.
#[derive(Debug, PartialEq, Clone)]
pub enum Literal<'a> {
    /// A char or byte char.
    CharLike { is_byte: bool, ch: char },
    /// A string, raw string, byte string or raw byte string.
    StrLike  { is_bytestr: bool, s: String },
    /// An interer type. If it has no type suffix, `ty` is None.
    IntLike  { ty: Option<Ty<'a>>, val: imax },
    /// An floating point type. If it has no type suffix, `ty` is None.
    FloatLike{ ty: Option<Ty<'a>>, val: fmax },
}

impl<'a> Eq for Literal<'a> {} // The float value is never NaN.
