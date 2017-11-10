#![cfg_attr(feature="clippy", feature(plugin))]
#![cfg_attr(feature="clippy", plugin(clippy))]

#[macro_use] extern crate lazy_static;
extern crate regex;

pub mod parse;
pub mod namesp;
