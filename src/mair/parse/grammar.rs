use pest::prelude::*;

impl_rdp! {
    grammar! {
        alpha    = _{ ['a'..'z'] | ['A'..'Z'] | ["_"] }
        nl       = _{ ["\r\n"] | ["\n"] | ["\r"] } // \f \v
        sp       = _{ [" "] | ["\t"] }
        ident    = @{ alpha ~ (alpha | ['0'..'9'])* ~ t_ }
        lifetime = @{ ["'"] ~ ident }
        t_       = _{ !(alpha | ['0'..'9']) } // end of ident

        // digit
        bin      = _{ ['0'..'1'] }
        oct      = _{ ['0'..'7'] }
        dec      = _{ ['0'..'9'] }
        hex      = _{ ['0'..'9'] | ['A'..'F'] | ['a'..'f'] }

        // symbols
        symbol   = {
            ["::"] | ["->"] | ["=>"] |
            ["=="] | ["!="] | ["<="] | [">="] |
            ["&&"] | ["||"] |
            ["!"] | ["="] |
            ["+="] | ["-="] | ["*="] | ["/="] | ["%="] |
            ["&="] | ["|="] | ["^="] | ["<<="] | [">>="] |
            ["+"] | ["-"] | ["*"] | ["/"] | ["%"] |
            ["&"] | ["|"] | ["^"] | ["<<"] | [">>"] |
            ["<"] | [">"] |
            ["$"] | ["#"] | [","] | [";"] | [":"] | ["."] | ["?"] | ["@"]
        }

        // comments & whitespaces
        line_comment       = _{
            ["//"] ~ (!["/"] ~ !["!"] | ["//"]) ~ line_comment_tail
        }
        block_comment      = _{
            ["/*"] ~ (!["*"] ~ !["!"] | ["**"]) ~ block_comment_tail
        }
        line_comment_tail  = _{ (!nl ~ any)* ~ nl }
        block_comment_tail = _{
            (!["/*"] ~ !["*/"] ~ any | block_comment)* ~ ["*/"]
        }
        comment    = _{ line_comment | block_comment }
        whitespace = _{ nl | sp }

        // tokenize
        tokens     = { whitespace* ~ token* }
        token      = {
            delimited |
            doc |
            ident | symbol | literal | lifetime
        }
        delimited  = {
            ["("] ~ tokens ~ [")"] |
            ["["] ~ tokens ~ ["]"] |
            ["{"] ~ tokens ~ ["}"]
        }

        // docs
        doc       = { outer_doc | inner_doc }
        outer_doc = {
            ["///"] ~ !["/"] ~ line_comment_tail |
            ["/**"] ~ !["*"] ~ block_comment_tail
        }
        inner_doc = {
            ["//!"] ~ line_comment_tail |
            ["/*!"] ~ block_comment_tail
        }

        // literals
        literal    = { char_lit | string_lit | int_lit | float_lit }

        // number literals
        int_lit      = @{ (
            ["0b"] ~ (bin | ["_"])+ |
            ["0o"] ~ (oct | ["_"])+ |
            ["0x"] ~ (hex | ["_"])+ |
            dec_lit
        ) ~ ident? }
        float_lit    = @{ (
            dec_lit ~
            (["."] ~ dec_lit)? ~
            ((["e"] | ["E"]) ~ dec_lit)?
        ) ~ ident? }
        dec_lit      = @{ (dec | ["_"])+ }

        // string-like literals
        char_lit    = @{ ["'"] ~ !["'"] ~ !nl ~ !sp ~ a_char ~ ["'"] }
        bchar_lit   = @{ ["b"] ~ char_lit }
        string_lit  = @{ normstr_lit | rawstr_lit }
        bstring_lit = @{ ["b"] ~ string_lit }
        normstr_lit = @{ ["\""] ~ (!["\""] ~ (escaped_nl | a_char))* ~ ["\""] }
        rawstr_lit  = @{
            ["r"] ~ [push(hashes)] ~ ["\""] ~
            (!(["\""] ~ [peek()]) | any)* ~
            ["\""] ~ [pop()]
        }
        hashes      = @{ ["#"]* }

        // char escape
        a_char         = @{ escaped | any }
        escaped_nl     = @{ ["\\"] ~ nl ~ sp* }
        escaped        = @{ ["\\"] ~ (simple_escape | ascii_escape | u_escape) }
        simple_escape  = @{ ["\\"] | ["n"] | ["r"] | ["t"] | ["0"] }
        ascii_escape   = @{ ["x"] ~ oct ~ hex }
        u_escape       = @{
            ["u"] ~ ["{"] ~
            hex ~ (hex ~ (hex ~ (hex ~ (hex ~ hex?)?)?)?)? ~
            ["}"]
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

#[test]
fn test_tokenize() {
    let mut parser = Rdp::new(StringInput::new(r##"
fn main() {
    println!("hello {}", "world");
}
    "##));
    println!("{} {}", parser.tokens(), parser.end());
    println!("{:?}", parser.queue());
    assert!(false);
}
