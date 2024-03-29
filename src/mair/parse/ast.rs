use std::cmp::Eq;
use std::rc::Rc;
use super::lexer::TokenKind;
pub use super::lexer::{SymbolType, KeywordType};

pub type LocStr<'a> = &'a str;

/// Integer type with the maximum width supported.
#[allow(non_camel_case_types)]
pub type imax = i64;

/// Floating point type with the maximum width supported.
#[allow(non_camel_case_types)]
pub type fmax = f64;

/// A module, a crate, or a rust source file.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Mod<'a> {
    pub attrs: Vec<Attr<'a>>,
    pub items: Vec<Item<'a>>,
}

/// An Item, which is the component of a crate/module.
pub type Item<'a> = ItemWrap<'a, ItemKind<'a>>;

/// An Item with detail type `T`.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct ItemWrap<'a, T> {
    pub attrs:  Vec<Attr<'a>>,
    pub is_pub: bool,
    pub detail: T,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum ItemKind<'a> {
    // https://doc.rust-lang.org/reference/items.html#items
    /// `extern` `crate` <name> `;`
    ExternCrate { name: Ident<'a> },
    /// `use <path>::*;`
    UseAll      { path: UsePath<'a> },
    /// `use <path>::<name> [as <alias>];`
    UseOne      { path: UsePath<'a>, name: UseName<'a> },
    /// `use <path>::{<name1> [as <alias1>], ... };`
    UseSome     { path: UsePath<'a>, names: Vec<UseName<'a>> },
    /// `mod <name>;`
    ExternMod   { name: Ident<'a> },
    /// `mod <name> { <item1> ... }`
    Mod         { name: Ident<'a>, items: Vec<Item<'a>> },
    /// `fn <sig>;`
    FuncDecl    { sig: Box<FuncSig<'a>> },
    /// `fn <sig> <body>`
    Func        { sig: Box<FuncSig<'a>>, body: Box<Expr<'a>> },
    /// `extern [abi] { <item1> ... }`
    Extern      { abi: ABI<'a>, items: Vec<ExternItem<'a>> },
    /// `type <alias> <template> [where_clause] [= <origin>];`
    Type        { alias:  Ident<'a>
                , templ:  Template<'a>
                , whs:    OptWhere<'a>
                , origin: Box<Ty<'a>> },
    /// `struct <name> <template> [where_clause];`
    StructUnit  { name:  Ident<'a>
                , templ: Template<'a>
                , whs:   OptWhere<'a> },
    /// `struct <name> <template> (<elem1>, ...) [where_clause];`
    StructTuple { name:  Ident<'a>
                , templ: Template<'a>
                , elems: Vec<StructTupleElem<'a>>
                , whs:   OptWhere<'a> },
    /// `struct <name> <template> [where_clause] { <field1>, ... }`
    StructFields{ name:   Ident<'a>
                , templ:  Template<'a>
                , whs:    OptWhere<'a>
                , fields: Vec<StructField<'a>> },
    /// `enum <name> <template> [where_clause] { <var1>, ... }`
    Enum        { name:  Ident<'a>
                , templ: Template<'a>
                , whs:   OptWhere<'a>
                , vars:  Vec<EnumVar<'a>> },
    /// `const <name>: <ty> = <val>;`
    Const       { name: Ident<'a>
                , ty:   Box<Ty<'a>>
                , val:  Box<Expr<'a>> },
    /// `static <name>: <ty> = <val>;`
    Static      { name: Ident<'a>
                , ty:   Box<Ty<'a>>
                , val:  Box<Expr<'a>> },
    /// `trait <name> <template> [where_clause] { <item1> ... }`
    Trait       { name:  Ident<'a>
                , templ: Template<'a>
                , base:  Option<Box<Ty<'a>>>
                , whs:   OptWhere<'a>
                , items: Vec<TraitItem<'a>> },
    /// `impl <template> <ty> [where_clause] { <item1> ... }`
    ImplType    { templ: Template<'a>
                , ty:    Box<Ty<'a>>
                , whs:   OptWhere<'a>
                , items: Vec<ImplItem<'a>> },
    /// `impl <template> <tr> for <ty> [where_clause] { <item1> ... }`
    ImplTrait   { templ: Template<'a>
                , tr:    Box<Trait<'a>>
                , ty:    Box<Ty<'a>>
                , whs:   OptWhere<'a>
                , items: Vec<ImplItem<'a>> },
    PluginInvoke(PluginInvoke<'a>),
}

/// A path in `use`.
#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub enum UsePath<'a> {
    Absolute{ comps: Vec<Ident<'a>> },
    Relative{ supers: usize, comps: Vec<Ident<'a>> },
}

/// A single name referred in a `use` declaration.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum UseName<'a> {
    Self_ (LocStr<'a>),
    Name  { name: Ident<'a>, alias: Option<Ident<'a>> },
}

pub type ExternItem<'a> = ItemWrap<'a, ExternItemKind<'a>>;

/// An item inside `extern` block.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum ExternItemKind<'a> {
    Func  { name:   Ident<'a>
          , args:   Vec<FuncParam<'a>>
          , is_va:  bool
          , ret_ty: Option<Box<Ty<'a>>> },
    Static{ name:  Ident<'a>
          , ty:    Option<Box<Ty<'a>>> }
}

pub type TraitItem<'a> = ItemWrap<'a, TraitItemKind<'a>>;

/// An item inside `trait` block.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum TraitItemKind<'a> {
    AssocTy{ name: Ident<'a>
           , default: Option<Box<Ty<'a>>> },
    Func   { sig:     Box<FuncSig<'a>>
           , default: Option<Box<Expr<'a>>> },
}

pub type ImplItem<'a> = ItemWrap<'a, ImplItemKind<'a>>;

/// An item inside `impl` block.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum ImplItemKind<'a> {
    AssocTy{ name:  Ident<'a>
           , val:   Box<Ty<'a>> },
    Func   { sig:   Box<FuncSig<'a>>
           , body:  Box<Expr<'a>> },
}

/// An element of a tuple-like struct or enum variant.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct StructTupleElem<'a> {
    pub attrs:  Vec<Attr<'a>>,
    pub is_pub: bool,
    pub ty:     Ty<'a>,
}

/// a field of a normal struct or enum variant.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct StructField<'a> {
    pub attrs:  Vec<Attr<'a>>,
    pub is_pub: bool,
    pub name:   Ident<'a>,
    pub ty:     Ty<'a>,
}

/// An variant of an `enum`.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum EnumVar<'a> {
    Unit  { attrs: Vec<Attr<'a>>, name: Ident<'a> },
    Tuple { attrs: Vec<Attr<'a>>
          , name: Ident<'a>
          , elems: Vec<StructTupleElem<'a>> },
    Struct{ attrs: Vec<Attr<'a>>
          , name: Ident<'a>
          , fields: Vec<StructField<'a>> },
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
    Self_  (LocStr<'a>),
    SelfTy_(LocStr<'a>),
    Super  (LocStr<'a>),
    Name   { name: Ident<'a>, hint: Option<Vec<TyHintArg<'a>>> },
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum TyHintArg<'a> {
    Lifetime(Lifetime<'a>),
    Ty      (Ty<'a>),
}

pub type Template<'a> = Vec<TemplArg<'a>>;

/// Template type or trait bound.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum TemplArg<'a> {
    Lifetime{ name: Lifetime<'a>, bound: Option<Vec<Lifetime<'a>>> },
    Ty      { name: Ident<'a>, bound: Option<Trait<'a>> },
}

pub type Where<'a> = Vec<Restrict<'a>>;
pub type OptWhere<'a> = Option<Where<'a>>;

/// A trait bound or lifetime restriction.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Restrict<'a> {
    LifeBound  { lt: Lifetime<'a>, bound: Vec<Lifetime<'a>> },
    TraitBound { ty: Ty<'a>, bound: Trait<'a> },
}

/// The signature of a function, including templates, trait bounds,
/// argument names and the function type.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct FuncSig<'a> {
    pub is_unsafe: bool,
    pub abi:       ABI<'a>,
    pub name:      Ident<'a>,
    pub templ:     Template<'a>,
    pub args:      Vec<FuncParam<'a>>,
    pub is_va:     bool,
    pub ret_ty:    Option<Box<Ty<'a>>>,
    pub whs:       OptWhere<'a>,
}

/// The signature of a lambda function.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct LambdaSig<'a> {
    pub is_move: bool,
    /// The location of capture list including `|`.
    pub loc:     LocStr<'a>,
    pub args:    Vec<FuncParam<'a>>,
    pub ret_ty:  Option<Box<Ty<'a>>>,
}

/// A parameter of a function.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum FuncParam<'a> {
    SelfMove{ is_mut: bool },
    SelfRef { is_mut: bool },
    SelfAs  (Ty<'a>),
    Bind    { pat: Pat<'a>, ty: Box<Ty<'a>> },
}

/// The type of a function.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct FuncTy<'a> {
    pub is_unsafe: bool,
    pub abi:       ABI<'a>,
    pub args:      Vec<FuncTyParam<'a>>,
    pub is_va:     bool,
    pub ret_ty:    Option<Box<Ty<'a>>>,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct FuncTyParam<'a> {
    pub name: Option<Ident<'a>>,
    pub ty:   Ty<'a>,
}

/// The ABI of a function or an `extern` block.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum ABI<'a> {
    Normal,
    Extern,
    Specific{ loc: LocStr<'a>, abi: Rc<String> },
}

/// A type.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Ty<'a> {
    /// The error type. Used in codes with syntax errors.
    Error,
    /// The placeholder `_`.
    Hole,
    /// The type `!`.
    Never,
    /// The type `Self`.
    Self_,
    /// An unsized type only with trait bounds.
    Traits (Vec<TyApply<'a>>),
    /// A generic type/trait applied with type paramaters, like `Vec<i32>`,
    /// `Iterator<Item=i32>`.
    /// No type arguments indicates a simple type/trait, like `i32`, `Copy`.
    Apply  (Box<TyApply<'a>>),
    /// A tuple type, like `(i32, i64)`.
    Tuple  (Vec<Ty<'a>>),
    /// A type inside paren.
    Paren  (Box<Ty<'a>>),
    /// Reference.
    Ref    { lt:     Option<Lifetime<'a>>
           , is_mut: bool
           , ty:     Box<Ty<'a>> },
    /// Pointer.
    Ptr    { is_mut: bool, ty: Box<Ty<'a>> },
    /// Slice.
    Slice  (Box<Ty<'a>>),
    /// Array.
    Array  { ty: Box<Ty<'a>>, size: Box<Expr<'a>> },
    /// The function pointer type, like `fn(i32, u8) -> usize`.
    Func   (Box<FuncTy<'a>>),
}
pub type Trait<'a> = Ty<'a>; // Types and traits are the same things at this
                             // time.

/// A simple type, specialized type or trait.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum TyApply<'a> {
    Angle { name: Path<'a>, args: Vec<TyApplyArg<'a>> },
    Paren { name: Path<'a>, args: Vec<Ty<'a>>, ret_ty: Option<Box<Ty<'a>>> },
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum TyApplyArg<'a> {
    Lifetime(Lifetime<'a>),
    Ty      (Ty<'a>),
    AssocTy { name: Ident<'a>, ty: Ty<'a> },
}

/// An attribute.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Attr<'a> {
    Doc { loc: LocStr<'a>, doc: &'a str },
    Meta(Meta<'a>),
}

/// An meta (the content inside `#[]`).
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Meta<'a> {
    /// A single meta name, like `test`, `macro_use`.
    Flag    (Ident<'a>),
    /// A key-value pair, like `crate_type = "lib"`, `recursion_limit="64"`.
    KeyValue{ key: Ident<'a>, value: Literal<'a> },
    /// A meta with a list of sub-meta arguments,
    /// like `cfg(target_os="linux")`.
    Sub     { name: Ident<'a>, subs: Vec<Meta<'a>> },
}

/// A statement.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Stmt<'a> {
    Item        (Box<Item<'a>>),
    Let         { pat:  Pat<'a>
                , ty:   Box<Ty<'a>>
                , expr: Box<Expr<'a>> },
    Expr        (Expr<'a>),
    PluginInvoke(PluginInvoke<'a>),
}

/// An expression.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Expr<'a> { // https://doc.rust-lang.org/reference/expressions.html
    /// The error expression. Used in codes with syntax errors.
    Error,
    Literal     (Literal<'a>),
    Path        (Path<'a>),
    Tuple       (Vec<Expr<'a>>),
    Paren       (Box<Expr<'a>>),
    Struct      { ty:     Box<Ty<'a>>
                , fields: Vec<ExprStructField<'a>>
                , base:   Option<Box<Expr<'a>>> },
    Block       { attrs: Vec<Attr<'a>>
                , stmts: Vec<Stmt<'a>>
                , ret:   Option<Box<Expr<'a>>> },
    Unsafe      (Box<Expr<'a>>),
    MemberCall  { obj:  Box<Expr<'a>>
                , func: PathComp<'a>
                , par_loc: LocStr<'a>
                , args: Vec<Expr<'a>> },
    StructField { obj: Box<Expr<'a>>, field: PathComp<'a> },
    TupleField  { obj: Box<Expr<'a>>, ind_loc: LocStr<'a>, index: imax },
    Index       { obj: Box<Expr<'a>>
                , brk_loc: LocStr<'a>
                , index: Box<Expr<'a>> },
    ArrayFill   { elem: Box<Expr<'a>>
                , len: Box<Expr<'a>> },
    ArrayLit    (Vec<Expr<'a>>),
    // Range is BinaryOp
    UnaryOp     { op: UnaryOp, op_loc: LocStr<'a>, expr: Box<Expr<'a>> },
    As          { expr: Box<Expr<'a>>, kw_loc: LocStr<'a>, ty: Box<Ty<'a>> },
    Colon       { expr: Box<Expr<'a>>, kw_loc: LocStr<'a>, ty: Box<Ty<'a>> },
    BinaryOp    { op: BinaryOp
                , op_loc: LocStr<'a>
                , l: Box<Expr<'a>>
                , r: Box<Expr<'a>> },
    Call        { func: Box<Expr<'a>>
                , par_loc: LocStr<'a>
                , args: Vec<Expr<'a>> },
    Lambda      { sig:  Box<LambdaSig<'a>>
                , body: Box<Expr<'a>> },
    Break       { label:  Option<Lifetime<'a>>
                , kw_loc: LocStr<'a>
                , expr:  Option<Box<Expr<'a>>> },
    Continue    { label: Option<Lifetime<'a>>, kw_loc: LocStr<'a> },
    Loop        { label:  Option<Lifetime<'a>>
                , body:   Box<Expr<'a>> },
    While       { label: Option<Lifetime<'a>>
                , cond: Box<Expr<'a>>
                , body: Box<Expr<'a>> },
    WhileLet    { pat:  Box<Pat<'a>>
                , expr: Box<Expr<'a>>
                , body: Box<Expr<'a>> },
    For         { label: Option<Lifetime<'a>>
                , pat:   Box<Pat<'a>>
                , iter:  Box<Expr<'a>>
                , body:  Box<Expr<'a>> },
    // else_expr ~ None          No else branch. ok.
    //           ~ Some(None)    `.. else <not {}>` err.
    //           ~ Some(Some(e)) `.. else <e>` ok.
    If          { cond:      Box<Expr<'a>>
                , then_expr: Box<Expr<'a>>
                , else_expr: Option<Box<Expr<'a>>> },
    IfLet       { pat:        Box<Pat<'a>>
                , match_expr: Box<Expr<'a>>
                , then_expr:  Box<Expr<'a>>
                , else_expr:  Option<Box<Expr<'a>>> },
    Match       { kw_loc: LocStr<'a>
                , expr:   Box<Expr<'a>>
                , arms:   Vec<MatchArm<'a>> },
    Return      { kw_loc: LocStr<'a>, expr: Option<Box<Expr<'a>>> },
    PluginInvoke(PluginInvoke<'a>),
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct ExprStructField<'a> {
    pub name: Ident<'a>,
    pub expr: Option<Box<Expr<'a>>>,
}

/// A match arm.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct MatchArm<'a> {
    pub pats: Vec<Pat<'a>>,
    pub cond: Option<Box<Expr<'a>>>,
    pub expr: Box<Expr<'a>>,
}

/// A pattern.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Pat<'a> {
    /// The hole `_`.
    Hole,
    /// A pattern with a variable bind. eg. `ref a@Some(_)`
    /// If `pat`, `ret_`, `mut_` are all None, it can be either a
    /// variant of an enum or a bind matching everything, like `None`.
    BindLike      { name:   Ident<'a>
                  , is_ref: bool
                  , is_mut: bool
                  , pat:    Option<Box<Pat<'a>>> },
    /// A path to a variant of unit-like enum or unit struct.
    Path          (Path<'a>),
    /// An literal. eg. `123`
    Literal       (Literal<'a>),
    /// A range patterns. eg. `1...2`, `'a'...'z'`
    Range         (Literal<'a>, Literal<'a>),
    /// A reference.
    Ref           (Box<Pat<'a>>),
    /// A tuple. eg. `(_, _)`
    Tuple         (Vec<Pat<'a>>),
    /// A pattern inside (redundant) paren.
    Paren         (Box<Pat<'a>>),
    /// A tuple-like enum variant or tuple struct. eg. `Some(1)`
    DestructTuple { name: Path<'a>, elems: Vec<Pat<'a>> },
    /// A struct-like enum variant or normal struct. eg. `Pt{ x: xx, y }`
    DestructNormal{ name: Path<'a>
                  , fields: Vec<DestructField<'a>>
                  , ellipsis: bool},
    /// A plugin/macro generating a pattern.
    PluginInvoke  (PluginInvoke<'a>),
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct DestructField<'a> {
    pub is_ref: bool,
    pub is_mut: bool,
    pub name:   Ident<'a>,
    pub pat:    Option<Box<Pat<'a>>>,
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
    pub name:  Ident<'a>,
    pub ident: Option<Ident<'a>>,
    pub tt:    TT<'a>, // must be TokenTree::Tree
}

/// A token tree with location.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum TTKind<'a> {
    Token(TokenKind<'a>),
    Tree{ delim: Delimiter, tts: Vec<TT<'a>> },
}

pub type TT<'a> = (TTKind<'a>, LocStr<'a>);

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum UnaryOp {
    // https://doc.rust-lang.org/grammar.html#unary-operator-expressions
    Try,
    Neg, Not,
    Borrow, BorrowMut, Deref,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum BinaryOp {
    // https://doc.rust-lang.org/grammar.html#binary-operator-expressions
    Add, Sub, Mul, Div, Mod,
    And, Or, Xor, Shl, Shr,
    LogAnd, LogOr,
    Equ, Ne, Lt, Gt, Le, Ge,
    /// `as` in `Expr`
    Range, RangeInclusive,
    Place,
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
    StrLike  { is_bytestr: bool, s: Rc<String> },
    /// An interer type. If it has no type suffix, `ty` is None.
    IntLike  { ty: Option<Box<Ty<'a>>>, val: imax },
    /// An floating point type. If it has no type suffix, `ty` is None.
    FloatLike{ ty: Option<Box<Ty<'a>>>, val: fmax },
    /// A boolean literal `true` or `false`.
    Bool     (bool),
}

pub type Ident<'a> = Result<LocStr<'a>, LocStr<'a>>;
pub type Lifetime<'a> = &'a str;

impl<'a> Eq for Literal<'a> {} // The float value is never NaN.

impl<'a> Ty<'a> {
    pub fn from_path(path: Path<'a>) -> Self {
        Ty::Apply(Box::new(TyApply::Angle{
            name: path,
            args: vec![],
        }))
    }

    pub fn from_name(name: &'a str) -> Self {
        Ty::from_path(Path{
            is_absolute: false,
            comps: vec![PathComp::Name{
                name: Ok(name),
                hint: None,
            }],
        })
    }

    pub fn unit() -> Self {
        Ty::Tuple(vec![])
    }
}

impl<'a> Expr<'a> {
    pub fn is_item_like(&self) -> bool {
        match *self {
            Expr::Block{ .. } |
            Expr::Loop{ .. } |
            Expr::While{ .. } |
            Expr::WhileLet{ .. } |
            Expr::For{ .. } |
            Expr::If{ .. } |
            Expr::IfLet{ .. } |
            Expr::Match{ .. } |
            Expr::PluginInvoke(PluginInvoke{
                tt: (TTKind::Tree{ delim: Delimiter::Brace, .. }, _),
                ..
            }) => true,
            _ => false,
        }
    }
}
