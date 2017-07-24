use std::cmp::Eq;
use super::lexer::{Loc, TokenKind};
use super::{imax, fmax};

/// A module, or a crate, as well as a rust source file.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Crate<'a> {
    pub attrs:  Vec<Attr<'a>>,
    pub items:  Vec<Item<'a>>,
}

/// An Item, which is the component of a crate/module.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Item<'a> {
    pub is_pub: bool,
    pub attrs:  Vec<Attr<'a>>,
    pub detail: ItemKind<'a>,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum ItemKind<'a> {
    // https://doc.rust-lang.org/reference/items.html#items
    /// `extern crate <name>;`
    ExternCrate { name: &'a str },
    /// `use <path>::*;`
    UseAll      { path: Path<'a> },
    /// `use <path>::<name> as <alias>;`
    /// `use <path>::{<name1> as <alias1>, ...};`
    UseSome     { path: Path<'a>, names: Vec<UseName<'a>> },
    /// `mod <name>;`
    ExternMod   { name: &'a str },
    /// `mod <name> { <item1> ... };`
    Mod         { name: &'a str, items: Vec<Item<'a>> },
    /// `fn <sig> <body>`
    /// `body` will be always an `Expr::Block`.
    Func        { sig: FuncSig<'a>, body: Expr<'a> },
    /// `extern [abi] { <item1> ... }`
    Extern      { abi: ABI<'a>, items: Vec<Item<'a>> },
    /// `type <alias> <template> [where_clause] = <origin>;`
    Type        { alias: &'a str, templ: Template<'a>, origin: Ty<'a> },
    /// `struct <name> <template> [where_clause];`
    StructUnit  { name: &'a str, templ: Template<'a> },
    /// `struct <name> <template> (<elem1>, ...) [where_clause];`
    StructTuple { name: &'a str, templ: Template<'a>, elems: Vec<StructTupleElem<'a>> },
    /// `struct <name> <template> [where_clause] { <field1>, ... }`
    StructNormal{ name: &'a str, templ: Template<'a>, fields: Vec<StructField<'a>> },
    /// `enum <name> <template> [where_clause] { <var1>, ... }`
    Enum        { name: &'a str, templ: Template<'a>, vars: Vec<EnumVar<'a>> },
    /// `const <name>: <ty> = <val>;`
    Const       { name: &'a str, ty: Ty<'a>, val: Expr<'a> },
    /// `static <name>: <ty> = <val>;`
    Static      { name: &'a str, ty: Ty<'a>, val: Expr<'a> },
    /// `trait <name> <template> [where_clause] { <item1> ... }`
    Trait       { name: &'a str, templ: Template<'a>, items: Vec<Item<'a>> },
    /// `impl <template> <ty> [where_clause] { <item1> ... }`
    ImplType    { templ: Template<'a>, ty: Ty<'a>, items: Vec<Item<'a>> },
    /// `impl <template> <trait_name> for <ty> [where_clause] { <item1> ... }`
    ImplTrait   { templ: Template<'a>, trait_name: TraitName<'a>, ty: Ty<'a>,
                  items: Vec<Item<'a>> },
    PluginInvoke(PluginInvoke<'a>),
}

/// The item or variable referred in a `use` declaration.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct UseName<'a> {
    pub name:  &'a str,
    pub alias: Option<&'a str>,
}

/// An element of a tuple-like struct or enum variant.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct StructTupleElem<'a> {
    pub is_pub: bool,
    pub attrs:  Vec<Attr<'a>>,
    pub ty:     Ty<'a>,
}

/// a field of a normal struct or enum variant.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct StructField<'a> {
    pub name:   &'a str,
    pub is_pub: bool,
    pub attrs:  Vec<Attr<'a>>,
    pub ty:     Ty<'a>,
}

/// An variant of an `enum`.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum EnumVar<'a> {
    Unit   { name: &'a str, attrs: Vec<Attr<'a>> },
    Tuple  { name: &'a str, attrs: Vec<Attr<'a>>, elems: Vec<StructTupleElem<'a>> },
    Struct { name: &'a str, attrs: Vec<Attr<'a>>, fields: Vec<StructField<'a>> },
}

/// A path, like `::std::Option`, `MyEnum::A`, etc.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Path<'a> {
    pub is_absolute: bool,
    pub comps:       Vec<PathComp<'a>>,
}

/// A path component, maybe with template hint (if any).
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum PathComp<'a> {
    Name  (&'a str),
    TyHint(Vec<Ty<'a>>),
}

/// Template types and trait bounds.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Template<'a> {
    pub lifetimes: Vec<Lifetime<'a>>,
    pub tys:       Vec<&'a str>,
    pub restricts: Vec<Restrict<'a>>,
}

/// A trait bound or lifetime restriction.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Restrict<'a> {
    TraitBound { ty: Ty<'a>, bound: TraitName<'a> },
    LifeBound  { lt: Lifetime<'a>, bound: Lifetime<'a> },
}

/// The signature of a function, including templates, trait bounds,
/// argument names and the function type.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct FuncSig<'a> {
    pub name:      &'a str,
    pub templ:     Template<'a>,
    pub self_arg:  SelfArg,
    pub arg_names: Vec<Pat<'a>>,
    pub ty:        FuncTy<'a>,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct FuncTy<'a> {
    pub is_unsafe: bool,
    /// Variable arguments
    pub is_va:     bool,
    pub abi:       ABI<'a>,
    pub args:      Vec<FuncArg<'a>>,
    pub ret_ty:    Ty<'a>,
}

/// An argument of function.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct FuncArg<'a> {
    pub pat: Pat<'a>,
    pub ty:  Ty<'a>,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum ABI<'a> {
    Normal,
    Extern,
    Specific(&'a str),
}

/// The argument `self`.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum SelfArg {
    /// No argument `self`. For static function or non-member-function.
    None,
    /// fn([mut] self, ...)
    Move   { is_mut: bool },
    /// fn(&[mut] self, ...)
    Borrow { is_mut: bool },
}

/// A type.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Ty<'a> {
    /// The placeholder `_`.
    Hole,
    /// The type `!`.
    Never,
    /// A generic type applied with type paramaters, like `Vec<i32>`.
    /// No type paramaters indicates a simple type, like `i32`.
    Apply (TyApply<'a>),
    /// A tuple type, like `(i32, i64)`.
    Tuple (Vec<Ty<'a>>),
    /// The pointer to a function, like `fn(i32, u8) -> usize`.
    Func  (Box<FuncTy<'a>>),
    /// Reference.
    Ref   { is_mut: bool, lifetime: Option<Lifetime<'a>>, inner: Box<Ty<'a>> },
    /// Pointers.
    Ptr   { is_mut: bool, inner: Box<Ty<'a>> },
    /// Slice.
    Slice (Box<Ty<'a>>),
    /// Array.
    Array { ty: Box<Ty<'a>>, size: imax },
}

/// A simple type, specialized type or trait name.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct TyApply<'a> {
    pub name:      Path<'a>,
    pub lifetimes: Vec<Lifetime<'a>>,
    pub params:    Vec<Ty<'a>>,
}
pub type TraitName<'a> = TyApply<'a>;

/// An attribute.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Attr<'a> {
    /// A single attribute name, like `test`, `macro_use`.
    Flag  (&'a str),
    /// A key-value pair, like `crate_type = "lib"`, `recursion_limit="64"`.
    Value { key: &'a str, value: Literal<'a> },
    /// An attribute with a list of sub-attribute arguments,
    /// like `cfg(target_os="linux")`.
    Sub   (&'a str, Vec<Attr<'a>>),
}

/// A statement.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Stmt<'a> {
    Item        (Item<'a>),
    Let         { pat: Pat<'a>, ty: Option<Ty<'a>>, expr: Expr<'a> },
    Expr        (Expr<'a>),
    PluginInvoke(PluginInvoke<'a>),
}

/// An expression.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Expr<'a> { // https://doc.rust-lang.org/reference/expressions.html
    Literal      (Literal<'a>),
    Path         (Path<'a>),
    Tuple        (Vec<Expr<'a>>),
    Struct       { ty: Ty<'a>, params: Vec<(&'a str, Expr<'a>)>, base: Option<Box<Expr<'a>>> },
    Block        { stmts: Vec<Stmt<'a>>, ret: Option<Box<Expr<'a>>> },
    MemberCall   { obj: Box<Expr<'a>>, func: &'a str, params: Vec<Expr<'a>> },
    TupleField   { obj: Box<Expr<'a>>, index: imax },
    StructField  { obj: Box<Expr<'a>>, member: &'a str },
    ArrayFill    { elem: Box<Expr<'a>>, len: Box<Expr<'a>> },
    ArrayLit     (Vec<Expr<'a>>),
    // Index is BinaryOp
    // Range is BinaryOp
    UnaryOp      (UnaryOp, Box<Expr<'a>>),
    AsOp         { expr: Box<Expr<'a>>, ty: Ty<'a> },
    RangeFromOp  (Box<Expr<'a>>),
    RangeToOp    (Box<Expr<'a>>),
    BinaryOp     (Box<Expr<'a>>, BinaryOp, Box<Expr<'a>>),
    Call         { func: Box<Expr<'a>>, params: Vec<Expr<'a>> },
    Lambda       { is_move: bool, sig: FuncSig<'a>, body: Box<Expr<'a>> },
    Loop         { label: Lifetime<'a>, body: Box<Expr<'a>> },
    Break        (Option<Lifetime<'a>>),
    Continue     (Option<Lifetime<'a>>),
    While        { label: Lifetime<'a>, cond: Box<Expr<'a>>, body: Box<Expr<'a>> },
    For          { label: Lifetime<'a>, iter: Pat<'a>, itee: Box<Expr<'a>>, body: Box<Expr<'a>> },
    If           { cond: Box<Expr<'a>>, then_expr: Box<Expr<'a>>, else_expr: Option<Box<Expr<'a>>> },
    Match        { expr: Box<Expr<'a>>, arms: Vec<MatchArm<'a>> },
    IfLet        { pat: Pat<'a>, cond: Box<Expr<'a>>,
                  then_expr: Box<Expr<'a>>, else_expr: Option<Box<Expr<'a>>> },
    WhileLet     { pat: Pat<'a>, cond: Box<Expr<'a>>, body: Box<Expr<'a>> },
    Return       (Option<Box<Expr<'a>>>),
    PluginInvoke (PluginInvoke<'a>),
}

/// A pattern.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Pat<'a> {
    /// The hole `_`.
    Hole,
    /// A pattern with a variable bind. eg. `a@1...9`
    Bind           { name: &'a str, pat: Box<Pat<'a>> },
    /// A unit-like enum variant or unit struct name, or a variable bind.
    /// eg. `Option::None`, `var`
    Var            (Path<'a>),
    /// An literal. eg. `123`
    Literal        (Literal<'a>),
    /// A range patterns. eg. `1...2`, `'a'...'z'`
    Range          (Literal<'a>, Literal<'a>),
    /// A tuple. eg. `(_, _)`
    Tuple          (Vec<Pat<'a>>),
    /// A tuple-like enum variant or tuple struct. eg. `Some(1)`
    DestructTuple  { name: Path<'a>, elems: Vec<Pat<'a>> },
    /// A struct-like enum variant or normal struct. eg. `Pt{ x: xx, y }`
    DestructNormal { name: Path<'a>, fields: Vec<DestructField<'a>>, ellipsis: bool},
    /// A plugin/macro generating a pattern.
    PluginInvoke   (PluginInvoke<'a>),
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct DestructField<'a> {
    pub field: &'a str,
    pub pat:   Option<Box<Pat<'a>>>,
}

/// A match arm.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct MatchArm<'a> {
    pub pats: Vec<Pat<'a>>,
    pub expr: Expr<'a>,
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

/// A plugin(including macro) invocation.
/// eg. `name! ( tts... )`
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct PluginInvoke<'a> {
    pub name:  &'a str,
    pub ident: Option<&'a str>,
    pub tt:    TT<'a>, // must be TokenTree::Tree
}

/// A token tree with location.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum TTKind<'a> {
    Token(TokenKind<'a>),
    Tree{ delim: Delimiter, tts: Vec<TT<'a>> },
}

pub type TT<'a> = (TTKind<'a>, Loc);

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum UnaryOp {
    // https://doc.rust-lang.org/grammar.html#unary-operator-expressions
    Neg, Deref, Not,
}


#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum BinaryOp {
    // https://doc.rust-lang.org/grammar.html#binary-operator-expressions
    Plus, Sub, Mul, Div, Mod,
    And, Or, Xor, Shl, Shr,
    LogAnd, LogOr,
    Equ, Ne, Lt, Gt, Le, Ge,
    /// `As` in `Expr`
    Range, RangeInclusive,
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

pub type Lifetime<'a> = &'a str;

impl<'a> Attr<'a> {
    pub fn from_doc(doc: &'a str) -> Self {
        Attr::Value{
            key: "doc",
            value: Literal::StrLike{
                is_bytestr: false,
                s: doc.to_string(),
            },
        }
    }
}

impl<'a> Eq for Literal<'a> {} // The float value is never NaN.

impl<'a> Ty<'a> {
    pub fn from_path(path: Path<'a>) -> Self {
        Ty::Apply(TyApply{ name: path, lifetimes: vec![], params: vec![] })
    }

    pub fn from_name(name: &'a str) -> Self {
        Ty::from_path(Path{
            is_absolute: false,
            comps: vec![PathComp::Name(name)],
        })
    }

    pub fn unit() -> Self {
        Ty::Tuple(vec![])
    }
}
