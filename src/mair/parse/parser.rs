use super::lexer::{TokenKind as Tokk, SymbolType, Token};
use super::ast::*;
use super::error::UnmatchedDelimError;
use super::putback_stream::PutbackStream;
use self::Delimiter::*;

pub struct Parser<'t>(PutbackStream<TT<'t>>);

/// Parse tokens into `TT`s.
pub fn parse_tts<'a>(toks: &[Token<'a>]) -> Result<Vec<TT<'a>>, UnmatchedDelimError> {
    let (rest, tts) = parse_tts_helper(toks)?;
    match rest.first() {
        None                => Ok(tts),
        Some(&(_, ref loc)) => Err(UnmatchedDelimError(loc.clone())),
    }
}

fn parse_tts_helper<'a, 'b>(mut toks: &'b [Token<'a>])
        -> Result<(&'b [Token<'a>], Vec<TT<'a>>), UnmatchedDelimError> {
    let mut tts = vec![];
    loop {
        match toks.first() {
            None | Some(&(Tokk::Delimiter{ is_open: false, .. }, _)) =>
                return Ok((toks, tts)),
            Some(&(Tokk::Delimiter{ is_open: true, delim }, ref loc)) => {
                let (rest, tts_inner) = parse_tts_helper(&toks[1..])?;
                toks = rest;
                match toks.first() {
                    None => return Err(UnmatchedDelimError(loc.clone())),
                    Some(&(Tokk::Delimiter{ is_open: false, delim: delim2 }, ref loc2)) => {
                        toks = &toks[1..];
                        if delim == delim2 {
                            tts.push((TTKind::Tree{
                                tts: tts_inner,
                                delim,
                            }, loc.start..loc2.end));
                        } else {
                            return Err(UnmatchedDelimError(loc2.clone()));
                        }
                    },
                    Some(_) => unreachable!(), // parse_tts_helper() only stops
                                               // before close delimiter or EOF
                }
            },
            Some(&(ref tokk, ref loc)) => {
                toks = &toks[1..];
                tts.push((TTKind::Token(tokk.clone()), loc.clone()));
            },
        }
    }
}

/// Parser a `.rs` file. It will never fail, and source with grammar errors will
/// be parsed into specific position (as TT) of AST.
pub fn parse_crate(tts: Vec<TT>) -> Mod {
    Parser::new(tts).eat_mod_end()
}

// Helper macros
macro_rules! tok {
    ($tok:pat) => { tok!($tok, _) };
    ($tok:pat, $loc:pat) => { (TTKind::Token($tok), $loc) };
}

macro_rules! tree {
    ($loc:pat, $($t:tt)*) => { (TTKind::Tree{$($t)*}, $loc) };
}

macro_rules! kw {
    ($s:tt) => { kw!($s, _) };
    ($s:tt, $loc:pat) => { tok!(Tokk::Keyword(keyword_type!($s)), $loc) };
}

macro_rules! sym {
    ($s:tt) => { sym!($s, _) };
    ($s:tt, $loc:pat) => { tok!(Tokk::Symbol(symbol_type!($s)), $loc) };
}

macro_rules! ident {
    ($p:pat) => { ident!($p, _) };
    ($p:pat, $loc:pat) => { tok!(Tokk::Ident($p), $loc) };
}

macro_rules! lt {
    ($p:pat) => { lt!($p, _) };
    ($p:pat, $loc:pat) => { tok!(Tokk::Lifetime($p), $loc) };
}

macro_rules! lit {
    ($p:pat) => { lit!($p, _) };
    ($p:pat, $loc:pat) => { tok!(Tokk::Literal($p), $loc) };
}

macro_rules! lit_str {
    () => { lit!(Literal::StrLike{ is_bytestr: false, .. }) };
    ($s:pat) => { lit_str!($s, _) };
    ($s:pat, $loc:pat) => {
        lit!(Literal::StrLike{ is_bytestr: false, s: $s }, $loc)
    };
}

impl<'t> Parser<'t> {
    pub fn new(tts: Vec<TT<'t>>) -> Self {
        Parser(PutbackStream::new(tts))
    }

    /// Take the rest of TTs.
    pub fn rest(self) -> Vec<TT<'t>> {
        self.0.rest()
    }

    /// Return whether there's no TT left.
    pub fn is_end(&self) -> bool {
        self.0.peek(0).is_none()
    }

    /// Eat and return many `p`s seperated by `sep` (without tailing `sep`)
    /// until `is_end` returns true. If the next TT after `p` is not `sep` , it
    /// will be converted by `err` and pushed into the result.
    fn eat_many<T, F, G, P>(
        &mut self,
        sep: SymbolType,
        mut is_end: F,
        mut err: G,
        mut p: P,
    ) -> Vec<T>
    where F: FnMut(&mut Self) -> bool,
          G: FnMut(TT<'t>) -> T,
          P: FnMut(&mut Self) -> T {
        if is_end(self) {
            return vec![];
        }
        let mut v = vec![];
        loop {
            v.push(p(self));
            'sep: loop {
                if is_end(self) {
                    return v;
                }
                match_eat!{ self.0;
                    tok!(Tokk::Symbol(sep_), loc) => if sep_ == sep {
                        break 'sep;
                    } else {
                        v.push(err((TTKind::Token(Tokk::Symbol(sep_)), loc)));
                    },
                    tok => v.push(err(tok)),
                    _ => return v, // no TT left
                }
            }
        }
    }

    /// Eat many `p`s seperated by `,` until the end. Return `p`s and whether
    /// it consumes tailing `,`.
    fn eat_many_comma_tail_end<T, G, P>(
        &mut self,
        err: G,
        p: P,
    ) -> (Vec<T>, bool)
    where G: FnMut(TT<'t>) -> T,
          P: FnMut(&mut Self) -> T {
        let mut tail = false;
        let v = self.eat_many(
            symbol_type!(","),
            |p_| match_eat!{ p_.0;
                t@sym!(",") => if p_.is_end() {
                    tail = true;
                    true
                } else {
                    p_.0.putback(t);
                    false
                },
                _ => p_.is_end(),
            },
            err,
            p,
        );
        (v, tail)
    }

    /// Eat inner attributes and then items to the end.
    pub fn eat_mod_end(&mut self) -> Mod<'t> {
        let inner_attrs = self.eat_inner_attrs();
        let mut items = vec![];
        while !self.is_end() {
            items.push(self.eat_item());
        }
        Mod{ inner_attrs, items }
    }

    /// Eat and return inner attributes and items inside `{}`, or return None.
    fn eat_opt_brace_mod(&mut self) -> Option<Mod<'t>> {
        match_eat!{ self.0;
            tree!(_, delim: Brace, tts) =>
                Some(Parser::new(tts).eat_mod_end()),
            _ => None,
        }
    }

    /// Eat and return an identifier, or return the empty str slice after the
    /// last TT eaten.
    fn eat_ident(&mut self) -> &'t str {
        unimplemented!()
    }

    /// Eat a semicolon, return whether it success.
    fn eat_semi(&mut self) -> bool {
        match_eat!{ self.0;
            sym!(";") => true,
            _ => false,
        }
    }

    /// Eat inner attributes as more as possible.
    fn eat_inner_attrs(&mut self) -> Vec<Attr<'t>> {
        let mut v = vec![];
        loop {
            match_eat!{ self.0;
                tok!(Tokk::InnerDoc(s)) => v.push(Attr::Doc(s)),
                sym!("#"), sym!("!"), tree!(_, delim: Bracket, tts) => {
                    let mut p = Parser::new(tts);
                    let meta = p.eat_meta();
                    v.push(Attr::Meta{ meta, unknow: p.rest() })
                },
                _ => return v,
            }
        }
    }

    /// Eat outer attributes as more as possible.
    fn eat_outer_attrs(&mut self) -> Vec<Attr<'t>> {
        let mut v = vec![];
        loop {
            match_eat!{ self.0;
                tok!(Tokk::OuterDoc(s)) => v.push(Attr::Doc(s)),
                sym!("#"), tree!(_, delim: Bracket, tts) => {
                    let mut p = Parser::new(tts);
                    let meta = p.eat_meta();
                    v.push(Attr::Meta{ meta, unknow: p.rest() })
                },
                _ => return v,
            }
        }
    }

    /// Eat a valid meta, or return Meta::Null without consuming any TT.
    fn eat_meta(&mut self) -> Meta<'t> {
        match_eat!{ self.0;
            ident!(key), sym!("="), lit!(value) =>
                Meta::KeyValue{ key, value },
            ident!(name), tree!(_, delim: Paren, tts) => {
                let mut p = Parser::new(tts);
                let (subs, _) = p.eat_many_comma_tail_end(
                    Meta::Unknow,
                    |p| p.eat_meta(),
                );
                Meta::Sub{ name, subs }
            },
            ident!(s) => Meta::Flag(s),
            _ => Meta::Null,
        }
    }

    /// Eat an item. It will consume at lease one TT.
    /// Warning: There must be at least one TT left.
    fn eat_item(&mut self) -> Item<'t> {
        let outer_attrs = self.eat_outer_attrs();
        let is_pub = match_eat!{ self.0;
            kw!("pub") => true,
            _ => false,
        };
        let opt_detail = self.eat_opt_item_detail();
        let detail = match opt_detail {
            Some(x) => x,
            None if outer_attrs.is_empty() && !is_pub => // havn't consumed
                match_eat!{ self.0;
                    tt => ItemKind::Unknow(tt),
                    _ => unreachable!(), // consumes nothing and nothing left
                },
            None => ItemKind::Null,
        };
        Item{ outer_attrs, is_pub, detail }
    }

    /// Eat and return the detail of an item, or return None.
    fn eat_opt_item_detail(&mut self) -> Option<ItemKind<'t>> {
        if let Some(p) = self.eat_opt_plugin_invoke() {
            return Some(ItemKind::PluginInvoke(p));
        }
        match_eat!{ self.0;
            kw!("extern"), kw!("crate") => Some(self.eat_extern_crate_tail()),
            kw!("use") => Some(self.eat_use_tail()),
            kw!("mod") => Some(self.eat_mod_tail()),
            kw!("fn") =>
                Some(self.eat_fn_tail(false, ABI::Normal)),
            kw!("extern"), kw!("fn") =>
                Some(self.eat_fn_tail(false, ABI::Extern)),
            kw!("extern"), lit_str!(abi), kw!("fn") =>
                Some(self.eat_fn_tail(false, ABI::Specific(abi))),
            kw!("unsafe"), kw!("fn") =>
                Some(self.eat_fn_tail(true, ABI::Normal)),
            kw!("unsafe"), kw!("extern"), kw!("fn") =>
                Some(self.eat_fn_tail(true, ABI::Extern)),
            kw!("unsafe"), kw!("extern"), lit_str!(abi), kw!("fn") =>
                Some(self.eat_fn_tail(true, ABI::Specific(abi))),
            kw!("extern") => Some(self.eat_extern_tail()),
            kw!("type")   => Some(self.eat_type_tail()),
            kw!("struct") => Some(self.eat_struct_tail()),
            kw!("enum")   => Some(self.eat_enum_tail()),
            kw!("const")  => Some(self.eat_const_static_tail(false)),
            kw!("static") => Some(self.eat_const_static_tail(true)),
            kw!("trait")  => Some(self.eat_trait_tail()),
            kw!("impl")   => Some(self.eat_impl_tail()),
            _ => None,
        }
    }

    /// Eat the tail after `extern crate`.
    fn eat_extern_crate_tail(&mut self) -> ItemKind<'t> {
        let name = self.eat_ident();
        let semi = self.eat_semi();
        ItemKind::ExternCrate{ name, semi }
    }

    /// Eat the tail after `use`.
    fn eat_use_tail(&mut self) -> ItemKind<'t> {
        match_eat!{ self.0; // `use` always uses absolute path
            sym!("::") => (),
            _ => (),
        };
        let mut comps = vec![];
        loop {
            match_eat!{ self.0;
                ident!(s), sym!("::") => comps.push(s),
                _ => break,
            }
        }
        let opt_names = self.eat_use_names();
        let semi = self.eat_semi();
        match opt_names {
            None => ItemKind::UseAll{ comps, semi },
            Some(names) => ItemKind::UseSome{ comps, names, semi },
        }
    }

    /// Eat and return the using names in item `use`, return None if `*`.
    fn eat_use_names(&mut self) -> Option<Vec<UseName<'t>>> {
        match_eat!{ self.0;
            sym!("*") => None,
            ident!(name) => Some(vec![UseName::Name{ name, alias: None }]),
            tree!(_, delim: Brace, tts) => {
                let (v, _) = Parser::new(tts).eat_many_comma_tail_end(
                    UseName::Unknow,
                    |p| {
                        let name = p.eat_ident();
                        let alias = match_eat!{ p.0;
                            kw!("as") => Some(p.eat_ident()),
                            _ => None,
                        };
                        UseName::Name{ name, alias }
                    },
                );
                Some(v)
            },
            _ => None,
        }
    }

    /// Eat the tail after `mod`.
    fn eat_mod_tail(&mut self) -> ItemKind<'t> {
        let name = self.eat_ident();
        if let Some(inner) = self.eat_opt_brace_mod() {
            ItemKind::Mod{ name, inner }
        } else {
            let semi = self.eat_semi();
            ItemKind::ExternMod{ name, semi }
        }
    }

    /// Eat the tail after `[unsafe] [extern [<abt>]] fn`.
    fn eat_fn_tail(&mut self, is_unsafe: bool, abi: ABI) -> ItemKind<'t> {
        let sig = Box::new(self.eat_fn_sig(is_unsafe, abi));
        if let Some(body) = self.eat_opt_block_expr() {
            ItemKind::Func{ sig, body: Box::new(body) }
        } else {
            let semi = self.eat_semi();
            ItemKind::FuncDecl{ sig, semi }
        }
    }

    /// Eat and return the signature of a function.
    fn eat_fn_sig(&mut self, is_unsafe: bool, abi: ABI) -> FuncSig<'t> {
        let name = self.eat_ident();
        let templ = self.eat_templ();
        let (args, is_va, ret, whs) = match_eat!{ self.0;
            tree!(_, delim: Paren, mut tts) => {
                let is_va = match tts.last() {
                    Some(&sym!("...")) => true,
                    _ => false,
                };
                if is_va { tts.pop(); }
                let (args, _) = Parser::new(tts).eat_many_comma_tail_end(
                    FuncParam::Unknow,
                    Parser::eat_func_param,
                );
                let ret = self.eat_opt_ret_ty();
                let whs = self.eat_opt_whs();
                (Some(args), is_va, ret, whs)
            },
            _ => (None, false, None, None),
        };
        FuncSig{ is_unsafe, abi, name, templ, args, is_va, ret, whs }
    }

    /// Eat and return a parameter of function.
    fn eat_func_param(&mut self) -> FuncParam<'t> {
        match_eat!{ self.0;
            sym!("&"), kw!("mut"), kw!("self") =>
                FuncParam::SelfRef{ is_mut: true },
            sym!("&"), kw!("self") =>
                FuncParam::SelfRef{ is_mut: false },
            kw!("self"), sym!(":") =>
                FuncParam::SelfAs(self.eat_ty()),
            kw!("mut"), kw!("self") =>
                FuncParam::SelfMove{ is_mut: true },
            kw!("self") =>
                FuncParam::SelfMove{ is_mut: false },
            _ => {
                let pat = self.eat_pat();
                let ty = match_eat!{ self.0;
                    sym!(":") => Some(Box::new(self.eat_ty())),
                    _ => None,
                };
                FuncParam::Bind{ pat, ty }
            },
        }
    }

    /// Eat the return type if the next TT is `->`, or return None.
    fn eat_opt_ret_ty(&mut self) -> Option<Box<Ty<'t>>> {
        match_eat!{ self.0;
            sym!("->") => Some(Box::new(self.eat_ty())),
            _ => None,
        }
    }

    /// Eat the tail after `extern` (item `extern`).
    fn eat_extern_tail(&mut self) -> ItemKind<'t> {
        let abi = match_eat!{ self.0;
            lit_str!(abi) => ABI::Specific(abi),
            _ => ABI::Extern,
        };
        let inner = self.eat_opt_brace_mod();
        ItemKind::Extern{ abi, inner }
    }

    /// Eat the tail after `type`.
    fn eat_type_tail(&mut self) -> ItemKind<'t> {
        let alias = self.eat_ident();
        let templ = self.eat_templ();
        let whs = self.eat_opt_whs();
        let origin = match_eat!{ self.0;
            sym!("=") => Some(Box::new(self.eat_ty())),
            _ => None,
        };
        let semi = self.eat_semi();
        ItemKind::Type{ alias, templ, whs, origin, semi }
    }

    /// Eat the tail after `struct`.
    fn eat_struct_tail(&mut self) -> ItemKind<'t> {
        let name = self.eat_ident();
        let templ = self.eat_templ();
        match_eat!{ self.0;
            tree!(_, delim: Paren, tts) => {
                let (elems, _) = Parser::new(tts).eat_many_comma_tail_end(
                    StructTupleElem::Unknow,
                    Parser::eat_struct_tuple_elem,
                );
                let whs = self.eat_opt_whs();
                let semi = self.eat_semi();
                ItemKind::StructTuple{ name, templ, elems, whs, semi }
            },
            _ => {
                let whs = self.eat_opt_whs();
                let opt_fields = match_eat!{ self.0;
                    tree!(_, delim: Brace, tts) => {
                        let (v, _) = Parser::new(tts).eat_many_comma_tail_end(
                            StructField::Unknow,
                            Parser::eat_struct_field,
                        );
                        Some(v)
                    },
                    _ => None,
                };
                if let Some(fields) = opt_fields {
                    ItemKind::StructFields{ name, templ, whs, fields }
                } else {
                    ItemKind::StructUnit{ name, templ, whs }
                }
            },
        }
    }

    /// Eat and return an element of tuple-like-struct.
    fn eat_struct_tuple_elem(&mut self) -> StructTupleElem<'t> {
        let attrs = self.eat_outer_attrs();
        let is_pub = match_eat!{ self.0;
            kw!("pub") => true,
            _ => false,
        };
        let ty = self.eat_ty();
        StructTupleElem::Elem{ attrs, is_pub, ty }
    }

    /// Eat and return a field of struct with fields.
    fn eat_struct_field(&mut self) -> StructField<'t> {
        let attrs = self.eat_outer_attrs();
        let is_pub = match_eat!{ self.0;
            kw!("pub") => true,
            _ => false,
        };
        let name = self.eat_ident();
        let ty = match_eat!{ self.0;
            sym!(":") => Some(self.eat_ty()),
            _ => None,
        };
        StructField::Field{ attrs, is_pub, name, ty }
    }

    /// Eat the tail after `enum`.
    fn eat_enum_tail(&mut self) -> ItemKind<'t> {
        let name = self.eat_ident();
        let templ = self.eat_templ();
        let whs = self.eat_opt_whs();
        let vars = match_eat!{ self.0;
            tree!(_, delim: Brace, tts) => {
                let (v, _) = Parser::new(tts).eat_many_comma_tail_end(
                    EnumVar::Unknow,
                    Parser::eat_enum_var,
                );
                Some(v)
            },
            _ => None,
        };
        ItemKind::Enum{ name, templ, whs, vars }
    }

    /// Eat a variant of `enum`.
    fn eat_enum_var(&mut self) -> EnumVar<'t> {
        let attrs = self.eat_outer_attrs();
        let name = self.eat_ident();
        match_eat!{ self.0;
            tree!(_, delim: Paren, tts) => {
                let (elems, _) = Parser::new(tts).eat_many_comma_tail_end(
                    StructTupleElem::Unknow,
                    Parser::eat_struct_tuple_elem,
                );
                EnumVar::Tuple{ attrs, name, elems }
            },
            tree!(_, delim: Brace, tts) => {
                let (fields, _) = Parser::new(tts).eat_many_comma_tail_end(
                    StructField::Unknow,
                    Parser::eat_struct_field,
                );
                EnumVar::Struct{ attrs, name, fields }
            },
            _ => EnumVar::Unit{ attrs, name },
        }
    }

    /// Eat the tail after `const` or `static`.
    fn eat_const_static_tail(&mut self, is_static: bool) -> ItemKind<'t> {
        let name = self.eat_ident();
        let ty = match_eat!{ self.0;
            sym!(":") => Some(Box::new(self.eat_ty())),
            _ => None,
        };
        let val = match_eat!{ self.0;
            sym!("=") => Some(Box::new(self.eat_expr(false))),
            _ => None,
        };
        if is_static {
            ItemKind::Static{ name, ty, val }
        } else {
            ItemKind::Const{ name, ty, val }
        }
    }

    /// Eat the tail after `trait`.
    fn eat_trait_tail(&mut self) -> ItemKind<'t> {
        let name = self.eat_ident();
        let base = match_eat!{ self.0;
            sym!(":") => Some(Box::new(self.eat_ty())),
            _ => None,
        };
        let whs = self.eat_opt_whs();
        let inner = self.eat_opt_brace_mod();
        ItemKind::Trait{ name, base, whs, inner }
    }

    /// Eat the tail after `impl`.
    fn eat_impl_tail(&mut self) -> ItemKind<'t> {
        let templ = self.eat_templ();
        let ty = self.eat_ty(); // trait_name can be
        match_eat!{ self.0;
            kw!("for") => {
                let trait_name = match ty {
                    Ty::Apply(x) => Some(x),
                    _ => None,
                };
                let ty = Box::new(self.eat_ty());
                let whs = self.eat_opt_whs();
                let inner = self.eat_opt_brace_mod();
                ItemKind::ImplTrait{ templ, trait_name, ty, whs, inner }
            },
            _ => {
                let whs = self.eat_opt_whs();
                let inner = self.eat_opt_brace_mod();
                ItemKind::ImplType{ templ, ty: Box::new(ty), whs, inner }
            },
        }
    }

    /// Eat and return a template (including `<>`), or return an empty
    /// template.
    fn eat_templ(&mut self) -> Template<'t> {
        unimplemented!()
    }

    /// Eat and return `where` clause, or return None.
    fn eat_opt_whs(&mut self) -> OptWhere<'t> {
        unimplemented!()
    }

    /// Eat and return a pat.
    fn eat_pat(&mut self) -> Pat<'t> {
        unimplemented!()
    }

    /// Eat and return a type.
    fn eat_ty(&mut self) -> Ty<'t> {
        unimplemented!()
    }

    /// Eat and return an expression. If `item_like_first` is true and the
    /// following TTs can be a item-like-expr, it will return immediately
    /// without checking binary ops. Eg. `m!{} - 1` will be parsed into `m!{}`
    /// and `-1` will be remained.
    fn eat_expr(&mut self, item_like_first: bool) -> Expr<'t> {
        unimplemented!()
    }

    /// Eat and return a block expression, or return None.
    fn eat_opt_block_expr(&mut self) -> Option<Expr<'t>> {
        unimplemented!()
    }

    /// Eat and return an plugin invoke, or return None.
    fn eat_opt_plugin_invoke(&mut self) -> Option<PluginInvoke<'t>> {
        match_eat!{ self.0;
            ident!(name), sym!("!") => {
                let ident = match_eat!{ self.0;
                    ident!(s) => Some(s),
                    _ => None,
                };
                let tt = match_eat!{ self.0;
                    t@tree!(_, ..) => Some(t),
                    _ => None,
                };
                Some(PluginInvoke{ name, ident, tt })
            },
            _ => None,
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use super::super::lexer::test::lex;
    use super::super::lexer::SymbolType as Sym;

    fn tts(input: &str) -> Result<Vec<TT>, UnmatchedDelimError> {
        let ltoks = lex(input).unwrap();
        parse_tts(&ltoks)
    }

    macro_rules! parse_check {
        ($s:expr, $f:ident, $ntt_rest:expr, $ret:expr) => {{
            let mut p = Parser::new(tts($s).unwrap());
            let r = p.$f();
            assert_eq!((r, p.rest().len()), ($ret, $ntt_rest));
        }};
    }

    #[test]
    fn tt_parser_test() {
        let star = |loc| (TTKind::Token(Tokk::Symbol(Sym::Mul)), loc);
        let tree = |delim, tts, loc| (TTKind::Tree{ delim, tts }, loc);
        assert_eq!(tts(" "), Ok(vec![]));
        assert_eq!(tts("*(* {*}[])"), Ok(vec![
            star(0..1),
            tree(Paren, vec![
                star(2..3),
                tree(Brace, vec![
                    star(5..6)
                ], 4..7),
                tree(Bracket, vec![], 7..9),
            ], 1..10),
        ]));
        let err = |loc| Err(UnmatchedDelimError(loc));
        assert_eq!(tts(" ("),  err(1..2));
        assert_eq!(tts("[("),  err(1..2));
        assert_eq!(tts(" (]"), err(2..3));
    }

    #[test]
    fn tt_parser_large_input() {
        use std::fs::File;
        use std::io::Read;
        let mut source = String::new();
        File::open(file!()).unwrap().read_to_string(&mut source).unwrap();
        let ret = tts(&source);
        println!("{:?}", ret);
        assert!(ret.is_ok());
    }

    #[test]
    fn parser_meta() {
        let tok_dol = TTKind::Token(Tokk::Symbol(symbol_type!("$")));
        parse_check!("", eat_meta, 0, Meta::Null);
        parse_check!("a[]", eat_meta, 1, Meta::Flag("a"));
        parse_check!("a(a=1,$$,,)", eat_meta, 0, Meta::Sub{
            name: "a",
            subs: vec![
                Meta::KeyValue{
                    key: "a",
                    value: Literal::IntLike{ ty: None, val: 1 },
                },
                Meta::Null,
                Meta::Unknow((tok_dol.clone(), 6..7)),
                Meta::Unknow((tok_dol.clone(), 7..8)),
                Meta::Null,
            ],
        });
    }
}
