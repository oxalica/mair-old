use std::ops::Range;

pub struct Interface<'a> {
    pub name:      &'a str,
    pub brief:     &'a str,
    pub scope:     Range<usize>,
    pub templates: Templates<'a>,
    pub if_type:   IFType<'a>,
}

pub enum IFType<'a> {
    Bind     (Type<'a>),
    TypeAlias(Type<'a>),
    NewType  (IFNewType<'a>, Impl<'a>, Vec<Trait<'a>>),
    Trait    (&'a str, Vec<TraitItem<'a>>),
}

pub enum IFNewType<'a> {
    StructUnit,
    StructTuple(Vec<Type<'a>>),
    Struct     (Vec<(&'a str, Type<'a>)>),
    Enum       (Vec<(&'a str, Vec<Type<'a>>)>),
}

pub enum Impl<'a> {
    Type(TypeName<'a>, Type<'a>),
    Func(Templates<'a>, Vec<Type<'a>>, Type<'a>),
}

pub enum TraitItem<'a> {
    Type(TypeName<'a>),
    Func(Templates<'a>, Vec<Type<'a>>, Type<'a>),
}

pub enum Type<'a> {
    Named(&'a str, Vec<Type<'a>>),
    Func (Vec<Type<'a>>, Box<Type<'a>>),
}

pub type Trait<'a> = (&'a str, Vec<Type<'a>>); // TraitName<T1, T2..>
pub type Templates<'a> = (Vec<TypeName<'a>>, Vec<TraitBound<'a>>);
pub type TypeName<'a> = &'a str;
pub type TraitBound<'a> = (Type<'a>, Trait<'a>);
