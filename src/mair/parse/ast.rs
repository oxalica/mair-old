use super::token::Token;

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
    attrs:  Vec<Attr<'a>>,
    is_pub: bool,
    ty:     Ty<'a>,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct StructField<'a> {
    attrs:  Vec<Attr<'a>>,
    is_pub: bool,
    name:   &'a str,
    ty:     Ty<'a>,
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
/// Note that type hint of a template function(`::<i32>` part in `func::<i32>`)
/// is not included.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Path<'a>(PathBegin<'a>, Vec<&'a str>);

/// The begining of a path.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum PathBegin<'a> {
    /// Begin with root, like `std`(in `use` declarations), `::std`, etc.
    ModRoot,
    /// Begin with self or super, like `func`(in expressions, `supers`: 0),
    /// `super::func`(`supers`: 1), `super::super::*`(`supers`: 2), etc.
    ModSelf{ supers: usize },
    /// Begin with a type, like `<i32>::max_value`, `<Option<_>>::default`,
    /// etc. Only be valid in expressions.
    Ty(Box<Ty<'a>>),
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
    Ref{ lifetime: &'a str, inner: Box<Ty<'a>> },
    /// Mutable reference.
    RefMut{ lifetime: &'a str, inner: Box<Ty<'a>> },
    /// Pointers.
    Ptr(Box<Ty<'a>>),
    /// Mutable pointers.
    PtrMut(Box<Ty<'a>>),
    // TODO: builtin types
}

/// The type of function.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum FuncTy<'a> {
    /// Diverging function, like `fn() -> !`
    Diverging(Vec<Ty<'a>>),
    /// Function without writing return type(default `()`), like `fn(i32)`.
    Action(Vec<Ty<'a>>),
    /// Other normal function, like `fn(i32) -> i32`.
    Normal(Vec<Ty<'a>>, Box<Ty<'a>>),
}

/// An attribute.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Attr<'a> {
    /// A single attribute name, like `test`, `macro_use`.
    Flag(&'a str),
    /// A key-value pair, like `crate_type = "lib"`, `recursion_limit="64"`.
    /// TODO: literal parsing.
    Value(&'a str, ()),
    /// An attribute with a list of sub-attribute arguments,
    /// like `cfg(target_os="linux")`.
    Sub(Vec<Attr<'a>>),
}

type FuncBody<'a> = Vec<Token<'a>>;
type Expr<'a> = Vec<Token<'a>>;
