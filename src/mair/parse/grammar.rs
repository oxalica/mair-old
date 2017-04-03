use pest::prelude::*;

impl_rdp! {
grammar! {
    // basic chars
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
    operator = {
        ["=="] | ["!="] | ["<="] | [">="] |
        ["&&"] | ["||"] |
        ["!"] | ["="] |
        ["+="] | ["-="] | ["*="] | ["/="] | ["%="] |
        ["&="] | ["|="] | ["^="] | ["<<="] | [">>="] |
        ["+"] | ["-"] | ["*"] | ["/"] | ["%"] |
        ["&"] | ["|"] | ["^"] | ["<<"] | [">>"] |
        ["<"] | [">"] |
        ["?"]
    }
    symbol = {
        ["::"] | ["->"] | ["=>"] |
        ["$"] | ["#"] | [","] | [";"] | [":"] | ["."] | ["@"]
    }

    // keywords
    kw_abstract = @{ ["abstract"] ~ t_ }
    kw_alignof  = @{ ["alignof"]  ~ t_ }
    kw_as       = @{ ["as"]       ~ t_ }
    kw_become   = @{ ["become"]   ~ t_ }
    kw_box      = @{ ["box"]      ~ t_ }
    kw_break    = @{ ["break"]    ~ t_ }
    kw_const    = @{ ["const"]    ~ t_ }
    kw_continue = @{ ["continue"] ~ t_ }
    kw_crate    = @{ ["crate"]    ~ t_ }
    kw_do       = @{ ["do"]       ~ t_ }
    kw_else     = @{ ["else"]     ~ t_ }
    kw_enum     = @{ ["enum"]     ~ t_ }
    kw_extern   = @{ ["extern"]   ~ t_ }
    kw_false    = @{ ["false"]    ~ t_ }
    kw_final    = @{ ["final"]    ~ t_ }
    kw_fn       = @{ ["fn"]       ~ t_ }
    kw_for      = @{ ["for"]      ~ t_ }
    kw_if       = @{ ["if"]       ~ t_ }
    kw_impl     = @{ ["impl"]     ~ t_ }
    kw_in       = @{ ["in"]       ~ t_ }
    kw_let      = @{ ["let"]      ~ t_ }
    kw_loop     = @{ ["loop"]     ~ t_ }
    kw_macro    = @{ ["macro"]    ~ t_ }
    kw_match    = @{ ["match"]    ~ t_ }
    kw_mod      = @{ ["mod"]      ~ t_ }
    kw_move     = @{ ["move"]     ~ t_ }
    kw_mut      = @{ ["mut"]      ~ t_ }
    kw_offsetof = @{ ["offsetof"] ~ t_ }
    kw_override = @{ ["override"] ~ t_ }
    kw_priv     = @{ ["priv"]     ~ t_ }
    kw_proc     = @{ ["proc"]     ~ t_ }
    kw_pub      = @{ ["pub"]      ~ t_ }
    kw_pure     = @{ ["pure"]     ~ t_ }
    kw_ref      = @{ ["ref"]      ~ t_ }
    kw_return   = @{ ["return"]   ~ t_ }
    kw_big_self = @{ ["Self"]     ~ t_ }
    kw_self     = @{ ["self"]     ~ t_ }
    kw_sizeof   = @{ ["sizeof"]   ~ t_ }
    kw_static   = @{ ["static"]   ~ t_ }
    kw_struct   = @{ ["struct"]   ~ t_ }
    kw_super    = @{ ["super"]    ~ t_ }
    kw_trait    = @{ ["trait"]    ~ t_ }
    kw_true     = @{ ["true"]     ~ t_ }
    kw_type     = @{ ["type"]     ~ t_ }
    kw_typeof   = @{ ["typeof"]   ~ t_ }
    kw_unsafe   = @{ ["unsafe"]   ~ t_ }
    kw_unsized  = @{ ["unsized"]  ~ t_ }
    kw_use      = @{ ["use"]      ~ t_ }
    kw_virtual  = @{ ["virtual"]  ~ t_ }
    kw_where    = @{ ["where"]    ~ t_ }
    kw_while    = @{ ["while"]    ~ t_ }
    kw_yield    = @{ ["yield"]    ~ t_ }

    // comments & whitespaces
    line_comment       = _{ ["//"] ~ (!["/"] ~ !["!"] | ["//"]) ~ line_comment_tail }
    block_comment      = _{ ["/*"] ~ (!["*"] ~ !["!"] | ["**"]) ~ block_comment_tail }
    line_comment_tail  = _{ (!nl ~ any)* ~ nl }
    block_comment_tail = _{ (!["/*"] ~ !["*/"] ~ any | block_comment)* ~ ["*/"] }
    comment            = _{ line_comment | block_comment }
    whitespace         = _{ nl | sp }

    // docs
    outer_doc = {
        ["///"] ~ !["/"] ~ line_comment_tail |
        ["/**"] ~ !["*"] ~ block_comment_tail
    }
    inner_doc = {
        ["//!"] ~ line_comment_tail |
        ["/*!"] ~ block_comment_tail
    }

    // attributes
    outer_attr =  { outer_doc | ["#"] ~ ["["] ~ attr_obj ~ ["]"] }
    inner_attr =  { inner_doc | ["#"] ~ ["!"] ~ ["["] ~ attr_obj ~ ["]"] }
    attr_obj   =  {
        ident ~ ["="] ~ attr_value |
        ident ~ (["("] ~ (attr_obj ~ ([","] ~ attr_obj)* ~ [","]?)? ~ [")"])?
    }
    attr_value = _{ literal }

    // >> literals
    literal = { char_lit | bchar_lit | string_lit | bstring_lit | int_lit | float_lit }
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
    // << literals

    // >> crate(module) & items
    module            =  { inner_attr* ~ item* }
    vis               =  { kw_pub? }
    item              =  { outer_attr* ~ vis ~ (
        item_extern_crate |
        item_use |
        item_mod |
        item_fn |
        item_extern |
        item_type |
        item_struct |
        item_enum |
        item_const |
        iten_static |
        item_trait |
        item_impl
    ) }
    item_extern_crate  =  { kw_extern ~ kw_crate ~ ident ~ (kw_as ~ ident)? ~ [";"] }
    item_use           =  { kw_use ~ use_path ~ [";"] }
        use_path       =  { ident ~ (["::"] ~ ident)* ~ (
            kw_as ~ ident |
            ["::"] ~ ["*"] |
            ["::"] ~ ["{"] ~ (ident ~ ([","] ~ ident)* ~ [","]?)? ~ ["}"]
        )? }
    item_mod           =  { kw_mod ~ ident ~ ["{"] ~ module ~ ["}"] }
    item_fn            =  { fn_head ~ block_expr }
        fn_head        =  {
            kw_fn ~ ident ~ template? ~
            ["("] ~ (fn_arg ~ ([","] ~ fn_arg)* ~ [","]?)? ~ [")"] ~ (["->"] ~ fn_ret)? ~
            where_clause?
        }
        fn_ret         =  { ["!"] | ty }
        fn_arg         =  { ident ~ [":"] ~ ty } // TODO: tuple match
        template       =  { (
            ["<"] ~ (lifetime ~ ([","] ~ lifetime)* | ident) ~ ([","] ~ ident)* ~ [">"]
        )? }
        where_clause   =  { kw_where ~ (ty ~ [":"] ~ trait_name)+ }
    item_extern        =  { kw_extern ~ string_lit? ~ ["{"] ~ fn_extern_decl* ~ ["}"] }
        fn_extern_decl =  { inner_attr* ~ fn_head ~ [";"] }
    item_type          =  { kw_type ~ ident ~ template? ~ ["="] ~ ty ~ [";"] }
    item_struct        =  { kw_struct ~ ident ~ template? ~ (
        [";"] |
        ty_tuple ~ [";"] |
        struct_body
    ) }
        struct_body    =  {
            ["{"] ~ (struct_field ~ ([","] ~ struct_field)* ~ [","]*)? ~ ["}"]
        }
        struct_field   =  { vis ~ ident ~ [":"] ~ ty }
    item_enum          =  { kw_enum ~ ident ~ template? ~
        ["{"] ~ (enum_field ~ ([","] ~ enum_field)* ~ [","]*)? ~ ["}"]
    }
        enum_field     =  { ident ~ (ty_tuple | struct_body)? }
    item_const         =  { kw_const ~ ident ~ [":"] ~ ty ~ ["="] ~ const_expr }
    iten_static        =  { kw_static ~ ident ~ [":"] ~ ty ~ ["="] ~ const_expr }
    item_trait         =  {
        kw_trait ~ ident ~ template? ~
        ["{"] ~ (trait_decl ~ ([","] ~ trait_decl)* ~ [","]?)? ~ ["}"]
    }
        trait_decl     =  { trait_decl_ty | trait_decl_fn }
        trait_decl_ty  =  { kw_type ~ ident ~ (["="] ~ ty)? ~ [";"] }
        trait_decl_fn  =  { fn_head ~ ([";"] | ["{"] ~ inner_attr* ~ block_expr ~ ["}"]) }
    item_impl          =  {
        kw_impl ~ template? ~ (ty | trait_name ~ kw_for ~ ty) ~
        ["{"] ~ (item_type | item_fn)* ~ ["}"]
    }
    // << crate(module) & items

    // type & trait_name
    ty         =  { ident } // TODO: other composite types
    ty_tuple   =  { ["("] ~ (ty ~ ([","] ~ ty)* ~ [","]?)? ~ [")"] }
    trait_name =  { ident ~ (["<"] ~ ty ~ ([","] ~ ty)* ~ [","]? ~ [">"])? }

    // expressions
    const_expr =  { any* } // TODO
    block_expr =  { any* } // TODO

    // crate
    crate_file = _{ whitespace* ~ module ~ eoi }
} // grammar!
} // impl_rdp!
