use pest::prelude::*;

impl_rdp! {
    grammar! {
        alpha    = _{ ['a'..'z'] | ['A'..'Z'] | ["_"] }
        newline  = _{ ["\r\n"] | ["\n"] | ["\r"] } // \f \v
        space    = _{ [" "] | ["\t"] }
        ident    = @{ alpha ~ (alpha | ['0'..'9'])* ~ t_ }
        lifetime = @{ ["'"] ~ ident }
        t_       = _{ !(alpha | ['0'..'9']) } // end of ident

        // comments
        line_comment       = _{
            ["//"] ~ (!["/"] ~ !["!"] | ["//"]) ~ line_comment_tail
        }
        block_comment      = _{
            ["/*"] ~ (!["*"] ~ !["!"] | ["**"]) ~ block_comment_tail
        }
        line_comment_tail  = _{ (!newline ~ any)* ~ newline }
        block_comment_tail = _{
            (!["/*"] ~ !["*/"] ~ any | block_comment)* ~ ["*/"]
        }
        comment    = _{ line_comment | block_comment }
        whitespace = _{ newline | space }

        // docs
        outer_doc = {
            ["///"] ~ !["/"] ~ line_comment_tail |
            ["/**"] ~ !["*"] ~ block_comment_tail
        }
        inner_doc = {
            ["//!"] ~ line_comment_tail |
            ["/*!"] ~ block_comment_tail
        }

        // items
        access        =  { (["pub"] ~ t_)? }
        item_ext_crt  =  {
            ["extern"] ~ t_ ~ ["crate"] ~ t_ ~ ident ~
            (["as"] ~ t_ ~ ident)? ~ [";"]
        }
        item_use      =  { access ~ ["use"] ~ t_ ~ use_path ~ [";"] }
        item_mod      =  {
            access ~ ["mod"] ~ t_ ~ ident ~ ["{"] ~ ["}"]  // TODO: module inner
        }
        item_fn       =  {
            access ~ ["fn"] ~ t_ ~ ident ~ template? ~
            ["("] ~ (fn_arg ~ ([","] ~ fn_arg)*)? ~ [")"] ~
            ["{"] ~ fn_inner ~ ["}"]
        }
        use_path      =  { ident ~ (["::"] ~ ident)* ~ (
            ["*"] |
            ["{"] ~ ident ~ ([","] ~ ident)* ~ ["}"]
        )? }
        fn_arg        =  { ident ~ [":"] ~ ty } // TODO: tuple match
        fn_inner      =  { any* } // TODO
        // TODO: other items
        template      =  { (
            ["<"] ~
            (lifetime ~ ([","] ~ lifetime)* | ident) ~ ([","] ~ ident)* ~
            [">"]
        )? }

        // ty
        ty = { ident } // TODO: other composite types
    }
}
