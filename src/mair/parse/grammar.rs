pub use self::parser::{
    parse_module,
    parse_item,
    parse_ty,
    parse_pat,
    parse_expr,
};

use super::ast::{Path, Template, TraitBound};

fn is_placeholder<'a>(x: &Path<'a>) -> bool {
    x.comps == vec![super::ast::PathComp{ body: "_", hint: None }]
}

fn merge_templ<'a>(mut templ: Template<'a>, mut whs: Vec<TraitBound<'a>>) -> Template<'a> {
    templ.trait_bounds.append(&mut whs);
    templ
}

mod parser {
    #![cfg_attr(feature="clippy", allow(clippy))]
    #![allow(unused_imports)]

    include!(concat!(env!("OUT_DIR"), "/mair/parse/grammar.rs"));
}
