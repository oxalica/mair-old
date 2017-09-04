use super::lexer::{TokenKind as Tokk, SymbolType, Token, LocStr};
use super::ast::*;
use super::error::UnmatchedDelimError;
use super::ttstream::TTStream;
use self::Delimiter::*;

pub struct Parser<'t>(TTStream<'t>);

/// Parse tokens into `TT`s.
pub fn parse_tts<'t>(
    source: &'t str,
    toks:   &[Token<'t>],
) -> Result<Vec<TT<'t>>, UnmatchedDelimError<'t>> {
    let (rest, tts) = parse_tts_helper(source, toks)?;
    match rest.first() {
        None            => Ok(tts),
        Some(&(_, loc)) => Err(UnmatchedDelimError(loc)),
    }
}

/// Return the string range between slice `l` and slice `r` of `source`
/// (Including `l` and `r`).
fn str_range<'a>(source: &'a str, l: &'a str, r: &'a str) -> &'a str {
    use super::str_ptr_diff;
    let pl = str_ptr_diff(l, source);
    let pr = str_ptr_diff(r, source);
    assert!(0 <= pl && pl as usize + l.len() <= source.len());
    assert!(0 <= pr && pr as usize + r.len() <= source.len());
    &source[pl as usize .. pr as usize + r.len()]
}

fn parse_tts_helper<'t, 'a>(
    source: &'t str,
    mut toks: &'a [Token<'t>],
) -> Result<(&'a [Token<'t>], Vec<TT<'t>>), UnmatchedDelimError<'t>> {
    let mut tts = vec![];
    loop {
        match toks.first() {
            None | Some(&(Tokk::Delimiter{ is_open: false, .. }, _)) =>
                return Ok((toks, tts)),
            Some(&(Tokk::Delimiter{ is_open: true, delim }, loc)) => {
                let (rest, tts_inner) = parse_tts_helper(source, &toks[1..])?;
                toks = rest;
                match toks.first() {
                    None => return Err(UnmatchedDelimError(loc)),
                    Some(&(Tokk::Delimiter{ is_open: false, delim: delim2 }, loc2)) => {
                        toks = &toks[1..];
                        if delim == delim2 {
                            tts.push((TTKind::Tree{
                                tts: tts_inner,
                                delim,
                            }, str_range(source, loc, loc2)));
                        } else {
                            return Err(UnmatchedDelimError(loc2));
                        }
                    },
                    Some(_) => unreachable!(), // parse_tts_helper() only stops
                                               // before close delimiter or EOF
                }
            },
            Some(&(ref tokk, loc)) => {
                toks = &toks[1..];
                tts.push((TTKind::Token(tokk.clone()), loc));
            },
        }
    }
}

/// Parser a `.rs` file. It will never fail, and source with grammar errors will
/// be parsed into specific position (as TT) of AST.
pub fn parse_crate<'t>(source: &'t str, tts: Vec<TT<'t>>) -> Mod<'t> {
    Parser::new(source, tts).eat_mod_end()
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
    ($s:pat) => { lit_str!($s, _) };
    ($s:pat, $loc:pat) => {
        lit!(Literal::StrLike{ is_bytestr: false, s: $s }, $loc)
    };
}
macro_rules! lit_int {
    ($i:pat) => { lit_int!($i, _) };
    ($i:pat, $loc:pat) => {
        lit!(Literal::IntLike{ ty: None, val: $i }, $loc)
    };
}

macro_rules! symBack {
    ($s:expr, $sym:tt, $loc:expr) => {
        $s.putback((
            TTKind::Token(Tokk::Symbol(symbol_type!($sym))),
            &$loc[1..],
        ))
    };
}

macro_rules! eatKw {
    ($s:expr; $kw:tt) => { match_eat!{ $s;
        kw!($kw, loc) => Some(loc),
        _ => None,
    }}
}

impl<'t> Parser<'t> {
    pub fn new(source: &'t str, tts: Vec<TT<'t>>) -> Self {
        Parser(TTStream::new(tts, &source[..0]))
    }

    fn new_inner(loc: LocStr<'t>, tts: Vec<TT<'t>>) -> Self {
        Parser(TTStream::new(tts, &loc[1..1])) // skip the first `(`
    }

    /// Take the rest of TTs.
    pub fn rest(self) -> Vec<TT<'t>> {
        self.0.rest()
    }

    /// Return whether there's no TT left.
    pub fn is_end(&self) -> bool {
        self.0.peek(0).is_none()
    }

    /// Eat `(<p> <sep>)* (<last> | <p>)? <is_end>` and return (`p`s, the
    /// optional `last`, whether there's a tailing `sep`).
    /// Unknow TTs between `p`, `sep`, `last` and `is_end` will be pushed into
    /// the result through `err`.
    fn eat_many_tail_last<T, U, F, G, H, P>(
        &mut self,
        sep: SymbolType,
        is_end: F,
        err: G,
        last: H,
        p: P,
    ) -> (Vec<T>, Option<U>, bool)
    where F: Fn(&mut Self) -> bool,
          G: Fn(TT<'t>) -> T,
          H: Fn(&mut Self) -> Option<U>,
          P: Fn(&mut Self) -> T {
        let mut v = vec![];
        let mut tail = false;
        'outer: loop {
            if is_end(self) {
                return (v, None, tail);
            }
            match last(self) {
                Some(u) => {
                    while !is_end(self) { // consume all after `last`
                        match_eat!{ self.0;
                            tt => v.push(err(tt)),
                            _ => unreachable!(), // not `is_end`
                        }
                    }
                    return (v, Some(u), false);
                },
                None => {
                    v.push(p(self));
                    while !is_end(self) { // expect `sep`
                        match_eat!{ self.0;
                            tok!(Tokk::Symbol(s), loc) => if s == sep {
                                tail = true;
                                continue 'outer;
                            } else {
                                v.push(err((
                                    TTKind::Token(Tokk::Symbol(s)),
                                    loc,
                                )));
                            },
                            tt => v.push(err(tt)),
                            _ => unreachable!(), // not `is_end`
                        }
                    }
                    return (v, None, false); // here `is_end`
                },
            }
        }
    }

    /// Eat `<p> (<sep> <p>)*` until `is_end` and return `p`s.
    fn eat_many_sep<T, F, G, P>(
        &mut self,
        sep: SymbolType,
        is_end: F,
        err: G,
        p: P,
    ) -> Vec<T>
    where F: Fn(&mut Self) -> bool,
          G: Fn(TT<'t>) -> T,
          P: Fn(&mut Self) -> T {
        let mut v = vec![];
        'outer: loop {
            v.push(p(self));
            while !is_end(self) {
                match_eat!{ self.0;
                    tok!(Tokk::Symbol(s), loc) => if s == sep {
                        continue 'outer;
                    } else {
                        v.push(err((
                            TTKind::Token(Tokk::Symbol(s)),
                            loc,
                        )));
                    },
                    tt => v.push(err(tt)),
                    _ => unreachable!(), // not `is_end`
                }
            }
            return v; // here `is_end`
        }
    }

    /// Eat many `p`s seperated by `sep` until `is_end`. Return `p`s and
    /// whether it consumes tailing `sep`.
    fn eat_many_tail<T, F, G, P>(
        &mut self,
        sep: SymbolType,
        is_end: F,
        err: G,
        p: P,
    ) -> (Vec<T>, bool)
    where F: Fn(&mut Self) -> bool,
          G: Fn(TT<'t>) -> T,
          P: Fn(&mut Self) -> T {
        enum Void {}
        let (v, _, tail): (_, Option<Void>, _) =
            self.eat_many_tail_last(sep, is_end, err, |_| None, p);
        (v, tail)
    }

    /// Eat many `p`s seperated by `,` until the end. Return `p`s and whether
    /// it consumes tailing `,`.
    fn eat_many_comma_tail_end<T, G, P>(
        mut self,
        err: G,
        p: P,
    ) -> (Vec<T>, bool)
    where G: Fn(TT<'t>) -> T,
          P: Fn(&mut Self) -> T {
        self.eat_many_tail(symbol_type!(","), |p| p.is_end(), err, p)
    }

    /// Return whether the next TT can be the start of an item.
    fn is_item_begin(&self) -> bool {
        match self.0.peek(0) {
            Some(&kw!("pub")) |
            Some(&kw!("extern")) |
            Some(&kw!("use")) |
            Some(&kw!("mod")) |
            Some(&kw!("fn")) |
            Some(&kw!("type")) |
            Some(&kw!("struct")) |
            Some(&kw!("enum")) |
            Some(&kw!("const")) | Some(&kw!("static")) |
            Some(&kw!("trait")) |
            Some(&kw!("impl")) =>
                true,
            Some(&kw!("unsafe")) => match self.0.peek(1) {
                Some(&kw!("fn")) |
                Some(&kw!("extern")) =>
                    true,
                _ => false,
            },
            _ => false,
        }
    }

    /// Return whether the next TT can be the start of a pattern.
    fn is_pat_begin(&self) -> bool {
        match self.0.peek(0) {
            Some(&ident!(_)) |
            Some(&sym!("::")) |
            Some(&lit!(_)) |
            Some(&kw!("ref")) | Some(&kw!("mut")) |
            Some(&tree!(_, delim: Paren, ..)) =>
                true,
            _ => false,
        }
    }

    /// Return whether the next TT can be the start of an expression.
    fn is_expr_begin(&self) -> bool {
        match self.0.peek(0) {
            Some(&lit!(_)) |
            Some(&lt!(_)) | // 'a: loop {}
            Some(&kw!("unsafe")) |
            Some(&kw!("super")) |
            Some(&kw!("self")) |
            Some(&kw!("Self")) | // Self{..}
            Some(&ident!(_)) | Some(&sym!("::")) |
            Some(&tree!(_, ..)) |
            Some(&sym!("-")) | Some(&sym!("!")) |
            Some(&sym!("&")) | Some(&sym!("*")) |
            Some(&sym!("..")) |
            Some(&sym!("|")) | Some(&sym!("||")) | Some(&kw!("move")) |
            Some(&kw!("break")) | Some(&kw!("continue")) |
            Some(&kw!("loop")) | Some(&kw!("while")) | Some(&kw!("for")) |
            Some(&kw!("if")) | Some(&kw!("match")) | Some(&kw!("return")) =>
                true,
            _ => false,
        }
    }

    /// Return an empty LocStr pointing at the end of previous TT (is any),
    /// or the beginning of source file.
    fn prev_pos(&self) -> LocStr<'t> {
        self.0.prev_last_pos()
    }

    /// Eat inner attributes and then items to the end.
    pub fn eat_mod_end(mut self) -> Mod<'t> {
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
            tree!(loc, delim: Brace, tts) =>
                Some(Parser::new_inner(loc, tts).eat_mod_end()),
            _ => None,
        }
    }

    /// Eat and return an identifier, or return the empty str slice after the
    /// last TT.
    fn eat_ident(&mut self) -> Ident<'t> {
        match_eat!{ self.0;
            ident!(s) => Ok(s),
            _ => Err(self.prev_pos()),
        }
    }

    /// Eat and return a Path.
    fn eat_path(&mut self) -> Path<'t> {
        let is_absolute = match_eat!{ self.0;
            sym!("::") => true,
            _ => false,
        };
        let mut comps = vec![self.eat_path_comp()];
        loop {
            match_eat!{ self.0;
                sym!("::") => comps.push(self.eat_path_comp()),
                _ => break,
            }
        }
        Path{ is_absolute, comps }
    }

    /// Eat and return a path component.
    fn eat_path_comp(&mut self) -> PathComp<'t> {
        match_eat!{ self.0;
            kw!("self", loc) => PathComp::Self_(loc),
            kw!("super", loc) => PathComp::Super(loc),
            _ => {
                let name = self.eat_ident();
                let hint = match_eat!{ self.0;
                    sym!("::"), sym!("<") => {
                        let (v, _) = self.eat_many_tail(
                            symbol_type!(","),
                            Parser::try_eat_templ_end,
                            TyHintArg::Unknow,
                            |p| match_eat!{ p.0;
                                lt!(lt) => TyHintArg::Lifetime(lt),
                                _ => TyHintArg::Ty(p.eat_ty(true)),
                            },
                        );
                        Some(v)
                    },
                    _ => None,
                };
                PathComp::Name{ name, hint }
            },
        }
    }

    /// Eat and return a semicolon.
    fn eat_semi(&mut self) -> Semi<'t> {
        match_eat!{ self.0;
            sym!(";") => Ok(()),
            _ => Err(self.prev_pos()),
        }
    }


    /// Eat inner attributes as more as possible.
    fn eat_inner_attrs(&mut self) -> Vec<Attr<'t>> {
        let mut v = vec![];
        loop {
            match_eat!{ self.0;
                tok!(Tokk::InnerDoc(doc), loc) =>
                    v.push(Attr::Doc{ loc, doc }),
                sym!("#"), sym!("!"), tree!(loc, delim: Bracket, tts) => {
                    let mut p = Parser::new_inner(loc, tts);
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
                tok!(Tokk::OuterDoc(doc), loc) =>
                    v.push(Attr::Doc{ loc, doc }),
                sym!("#"), tree!(loc, delim: Bracket, tts) => {
                    let mut p = Parser::new_inner(loc, tts);
                    let meta = p.eat_meta();
                    v.push(Attr::Meta{ meta, unknow: p.rest() })
                },
                _ => return v,
            }
        }
    }

    /// Eat a valid meta, or return Meta::Null without consuming any TT.
    fn eat_meta(&mut self) -> Meta<'t> {
        let name = self.eat_ident();
        match_eat!{ self.0;
            sym!("="), lit!(value) =>
                Meta::KeyValue{ key: name, value },
            tree!(loc, delim: Paren, tts) => {
                let (subs, _) = Parser::new_inner(loc, tts)
                                       .eat_many_comma_tail_end(
                    Meta::Unknow,
                    |p| p.eat_meta(),
                );
                Meta::Sub{ name, subs }
            },
            _ => Meta::Flag(name),
        }
    }

    /// Eat an item. It will consume at lease one TT.
    /// Warning: There must be at least one TT left.
    fn eat_item(&mut self) -> Item<'t> {
        let outer_attrs = self.eat_outer_attrs();
        let pub_ = eatKw!(self.0; "pub");
        let opt_detail = self.eat_opt_item_detail();
        let detail = match opt_detail {
            Some(x) => x,
            None if outer_attrs.is_empty() && pub_.is_none() =>
                match_eat!{ self.0;         // havn't consumed `pub`
                    tt => ItemKind::Unknow(tt),
                    _ => unreachable!(), // consumes nothing and nothing left
                },
            None => ItemKind::Null,
        };
        Item{ outer_attrs, pub_, detail }
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
                Some(self.eat_fn_tail(None, ABI::Normal)),
            kw!("extern"), kw!("fn") =>
                Some(self.eat_fn_tail(None, ABI::Extern)),
            kw!("extern"), lit_str!(abi, loc), kw!("fn") =>
                Some(self.eat_fn_tail(None, ABI::Specific{ loc, abi })),
            kw!("unsafe", lu), kw!("fn") =>
                Some(self.eat_fn_tail(Some(lu), ABI::Normal)),
            kw!("unsafe", lu), kw!("extern"), kw!("fn") =>
                Some(self.eat_fn_tail(Some(lu), ABI::Extern)),
            kw!("unsafe", lu), kw!("extern"), lit_str!(abi, loc), kw!("fn") =>
                Some(self.eat_fn_tail(Some(lu), ABI::Specific{ loc, abi })),
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
        let is_absolute = match_eat!{ self.0;
            sym!("::") => true,
            _ => false,
        };
        let mut comps = vec![];
        loop {
            match_eat!{ self.0;
                kw!("self", loc), sym!("::") =>
                    comps.push(PathComp::Self_(loc)),
                kw!("super", loc), sym!("::") =>
                    comps.push(PathComp::Super(loc)),
                ident!(name), sym!("::") =>
                    comps.push(PathComp::Name{ name: Ok(name), hint: None }),
                sym!("::") => {
                    let loc = self.prev_pos();
                    comps.push(PathComp::Name{ name: Err(loc), hint: None })
                },
                _ => break,
            }
        }
        self.eat_use_names_tail(Path{ is_absolute, comps })
    }

    /// Eat the using names and semicolon in item `use`, return the ItemKind.
    fn eat_use_names_tail(&mut self, path: Path<'t>) -> ItemKind<'t> {
        match_eat!{ self.0;
            sym!("*") => {
                let semi = self.eat_semi();
                ItemKind::UseAll{ path, semi }
            },
            tree!(loc, delim: Brace, tts) => {
                let (names, _) = Parser::new_inner(loc, tts)
                                        .eat_many_comma_tail_end(
                    UseName::Unknow,
                    Parser::eat_use_name,
                );
                let semi = self.eat_semi();
                ItemKind::UseSome{ path, names, semi }
            },
            _ => {
                let name = self.eat_use_name();
                let semi = self.eat_semi();
                ItemKind::UseOne{ path, name, semi }
            },
        }
    }

    /// Eat and return a UseName like `self` or `name [as alias]`.
    fn eat_use_name(&mut self) -> UseName<'t> {
        match_eat!{ self.0;
            kw!("self", loc) => UseName::Self_(loc),
            _ => {
                let name = self.eat_ident();
                let alias = match_eat!{ self.0;
                    kw!("as") => Some(self.eat_ident()),
                    _ => None,
                };
                UseName::Name{ name, alias }
            },
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
    fn eat_fn_tail(
        &mut self,
        unsafe_: OptSym<'t>,
        abi: ABI<'t>,
    ) -> ItemKind<'t> {
        let sig = Box::new(self.eat_fn_sig(unsafe_, abi));
        if let Some(body) = self.eat_opt_block_expr() {
            ItemKind::Func{ sig, body: Box::new(body) }
        } else {
            let semi = self.eat_semi();
            ItemKind::FuncDecl{ sig, semi }
        }
    }

    /// Eat and return the signature of a function.
    fn eat_fn_sig(
        &mut self,
        unsafe_: OptSym<'t>,
        abi: ABI<'t>,
    ) -> FuncSig<'t> {
        let name = self.eat_ident();
        let templ = self.eat_templ();
        let (args, va) = match_eat!{ self.0;
            tree!(loc, delim: Paren, tts) => {
                let (args, va, _) = Parser::new_inner(loc, tts)
                                           .eat_many_tail_last(
                    symbol_type!(","),
                    |p| p.is_end(),
                    FuncParam::Unknow,
                    |p| match_eat!{ p.0;
                        sym!("...", loc) => Some(loc),
                        _ => None,
                    },
                    Parser::eat_func_param,
                );
                (Some(args), va)
            },
            _ => (None, None),
        };
        let ret_ty = self.eat_opt_ret_ty();
        let whs = self.eat_opt_whs();
        FuncSig{ unsafe_, abi, name, templ, args, va, ret_ty, whs }
    }

    /// Eat and return a parameter of function.
    fn eat_func_param(&mut self) -> FuncParam<'t> {
        match_eat!{ self.0;
            sym!("&"), kw!("mut", loc), kw!("self") =>
                FuncParam::SelfRef{ mut_: Some(loc) },
            sym!("&"), kw!("self") =>
                FuncParam::SelfRef{ mut_: None },
            kw!("self"), sym!(":") =>
                FuncParam::SelfAs(self.eat_ty(true)),
            kw!("mut", loc), kw!("self") =>
                FuncParam::SelfMove{ mut_: Some(loc) },
            kw!("self") =>
                FuncParam::SelfMove{ mut_: None },
            _ => {
                let pat = self.eat_pat();
                let ty = match_eat!{ self.0;
                    sym!(":") => Some(Box::new(self.eat_ty(true))),
                    _ => None,
                };
                FuncParam::Bind{ pat, ty }
            },
        }
    }

    /// Eat the return type if the next TT is `->`, or return None.
    fn eat_opt_ret_ty(&mut self) -> Option<Box<Ty<'t>>> {
        match_eat!{ self.0;
            sym!("->") => Some(Box::new(self.eat_ty(true))),
            _ => None,
        }
    }

    /// Eat the tail after `extern` (item `extern`).
    fn eat_extern_tail(&mut self) -> ItemKind<'t> {
        let abi = match_eat!{ self.0;
            lit_str!(abi, loc) => ABI::Specific{ loc, abi },
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
            sym!("=") => Some(Box::new(self.eat_ty(true))),
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
            tree!(loc, delim: Paren, tts) => {
                let (elems, _) = Parser::new_inner(loc, tts)
                                        .eat_many_comma_tail_end(
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
                    tree!(loc, delim: Brace, tts) => {
                        let (v, _) = Parser::new_inner(loc, tts)
                                            .eat_many_comma_tail_end(
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
                    let semi = self.eat_semi();
                    ItemKind::StructUnit{ name, templ, whs, semi }
                }
            },
        }
    }

    /// Eat and return an element of tuple-like-struct.
    fn eat_struct_tuple_elem(&mut self) -> StructTupleElem<'t> {
        let attrs = self.eat_outer_attrs();
        let pub_ = match_eat!{ self.0;
            kw!("pub", loc) => Some(loc),
            _ => None,
        };
        let ty = self.eat_ty(true);
        StructTupleElem::Elem{ attrs, pub_, ty }
    }

    /// Eat and return a field of struct with fields.
    fn eat_struct_field(&mut self) -> StructField<'t> {
        let attrs = self.eat_outer_attrs();
        let pub_ = eatKw!(self.0; "pub");
        let name = self.eat_ident();
        let ty = match_eat!{ self.0;
            sym!(":") => Some(self.eat_ty(true)),
            _ => None,
        };
        StructField::Field{ attrs, pub_, name, ty }
    }

    /// Eat the tail after `enum`.
    fn eat_enum_tail(&mut self) -> ItemKind<'t> {
        let name = self.eat_ident();
        let templ = self.eat_templ();
        let whs = self.eat_opt_whs();
        let vars = match_eat!{ self.0;
            tree!(loc, delim: Brace, tts) => {
                let (v, _) = Parser::new_inner(loc, tts)
                                    .eat_many_comma_tail_end(
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
            tree!(loc, delim: Paren, tts) => {
                let (elems, _) = Parser::new_inner(loc, tts)
                                        .eat_many_comma_tail_end(
                    StructTupleElem::Unknow,
                    Parser::eat_struct_tuple_elem,
                );
                EnumVar::Tuple{ attrs, name, elems }
            },
            tree!(loc, delim: Brace, tts) => {
                let (fields, _) = Parser::new_inner(loc, tts)
                                         .eat_many_comma_tail_end(
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
            sym!(":") => Some(Box::new(self.eat_ty(true))),
            _ => None,
        };
        let val = match_eat!{ self.0;
            sym!("=") => Some(Box::new(self.eat_expr(false, true))),
            _ => None,
        };
        let semi = self.eat_semi();
        if is_static {
            ItemKind::Static{ name, ty, val, semi }
        } else {
            ItemKind::Const{ name, ty, val, semi }
        }
    }

    /// Eat the tail after `trait`.
    fn eat_trait_tail(&mut self) -> ItemKind<'t> {
        let name = self.eat_ident();
        let templ = self.eat_templ();
        let base = match_eat!{ self.0;
            sym!(":") => Some(Box::new(self.eat_ty(true))),
            _ => None,
        };
        let whs = self.eat_opt_whs();
        let inner = self.eat_opt_brace_mod();
        ItemKind::Trait{ name, templ, base, whs, inner }
    }

    /// Eat the tail after `impl`.
    fn eat_impl_tail(&mut self) -> ItemKind<'t> {
        let templ = self.eat_templ();
        let ty = Box::new(self.eat_ty(true));
        match_eat!{ self.0;
            kw!("for") => {
                let tr = ty;
                let ty = Box::new(self.eat_ty(true));
                let whs = self.eat_opt_whs();
                let inner = self.eat_opt_brace_mod();
                ItemKind::ImplTrait{ templ, tr, ty, whs, inner }
            },
            _ => {
                let whs = self.eat_opt_whs();
                let inner = self.eat_opt_brace_mod();
                ItemKind::ImplType{ templ, ty, whs, inner }
            },
        }
    }

    /// If the next TT starts with `>`, eat `>` and return true. Otherwise,
    /// return false.
    fn try_eat_templ_end(&mut self) -> bool {
        match_eat!{ self.0;
            sym!(">") => true,
            sym!(">>" , loc) => { symBack!(self.0, ">" , loc); true },
            sym!(">=" , loc) => { symBack!(self.0, "=" , loc); true },
            sym!(">>=", loc) => { symBack!(self.0, ">=", loc); true },
            _ => false,
        }
    }

    /// Eat and return a template (including `<>`), or return an empty
    /// template.
    fn eat_templ(&mut self) -> Template<'t> {
        match_eat!{ self.0;
            sym!("<") => {
                let (v, _) = self.eat_many_tail(
                    symbol_type!(","),
                    |p| p.try_eat_templ_end(),
                    TemplArg::Unknow,
                    Parser::eat_templ_arg,
                );
                v
            },
            _ => vec![],
        }
    }

    /// Eat a template argument.
    fn eat_templ_arg(&mut self) -> TemplArg<'t> {
        match_eat!{ self.0;
            lt!(name) => {
                let bound = match_eat!{ self.0;
                    sym!(":") => Some(self.eat_lifetime_bound()),
                    _ => None,
                };
                TemplArg::Lifetime{ name, bound }
            },
            _ => {
                let name = self.eat_ident();
                let bound = match_eat!{ self.0;
                    sym!(":") => Some(self.eat_ty(true)),
                    _ => None,
                };
                TemplArg::Ty{ name, bound }
            },
        }
    }

    /// Eat and return `'lt1 + 'lt2 + ...`.
    fn eat_lifetime_bound(&mut self) -> Vec<Lifetime<'t>> {
        self.eat_many_tail(
            symbol_type!("+"),
            |p| match p.0.peek(0) {
                Some(&lt!(_)) |
                Some(&sym!("+")) => false,
                _ => true,
            },
            |_| unreachable!(),  // if the next TT is not a lifetime, `end`
            |p| match_eat!{ p.0; // will return true to stop eating.
                lt!(x) => x,
                _ => unreachable!(), //
            },
        ).0
    }

    /// Eat and return `where` clause, or return None.
    fn eat_opt_whs(&mut self) -> OptWhere<'t> {
        match_eat!{ self.0;
            kw!("where") => {
                let (restricts, _) = self.eat_many_tail(
                    symbol_type!(","),
                    |p| match p.0.peek(0) {
                        Some(&tree!(_, delim: Brace, ..)) |
                        Some(&sym!("->")) |
                        Some(&sym!(";")) => true,
                        _ => false,
                    },
                    Restrict::Unknow,
                    Parser::eat_restrict,
                );
                Some(restricts)
            },
            _ => None,
        }
    }

    /// Eat a restriction of where clause.
    fn eat_restrict(&mut self) -> Restrict<'t> {
        match_eat!{ self.0;
            lt!(lt) => {
                let bound = match_eat!{ self.0;
                    sym!(":") => Some(self.eat_lifetime_bound()),
                    _ => None,
                };
                Restrict::LifeBound{ lt, bound }
            },
            _ => {
                let ty = self.eat_ty(true);
                let bound = match_eat!{ self.0;
                    sym!(":") => Some(self.eat_ty(true)),
                    _ => None,
                };
                Restrict::TraitBound{ ty, bound }
            },
        }
    }

    /// Eat and return a pat.
    fn eat_pat(&mut self) -> Pat<'t> {
        if let Some(p) = self.eat_opt_plugin_invoke() {
            return Pat::PluginInvoke(p);
        }
        match_eat!{ self.0;
            ident!("_") => Pat::Hole,
            lit!(lit) => match_eat!{ self.0;
                sym!("..."), lit!(lit2) => Pat::Range(lit, lit2),
                _ => Pat::Literal(lit),
            },
            sym!("&") =>
                Pat::Ref(Box::new(self.eat_pat())),
            tree!(loc, delim: Paren, tts) => {
                let (mut v, tail) = Parser::new_inner(loc, tts)
                                           .eat_many_comma_tail_end(
                    Pat::Unknow,
                    Parser::eat_pat,
                );
                if v.len() == 1 && !tail {
                    Pat::Paren(Box::new(v.pop().unwrap()))
                } else {
                    Pat::Tuple(v)
                }
            },
            _ => {
                let ref_ = eatKw!(self.0; "ref");
                let mut_ = eatKw!(self.0; "mut");
                if ref_.is_some() || mut_.is_some() {
                    let name = self.eat_ident();
                    let pat = match_eat!{ self.0;
                        sym!("@") => Some(Box::new(self.eat_pat())),
                        _ => None,
                    };
                    Pat::BindLike{ name, ref_, mut_, pat }
                } else {
                    self.eat_pat_pathy()
                }
            },
        }
    }

    /// Eat a pattern starting with an identifier,
    fn eat_pat_pathy(&mut self) -> Pat<'t> {
        let name = self.eat_path();
        match_eat!{ self.0;
            tree!(loc, delim: Paren, tts) => {
                let (v, _) = Parser::new_inner(loc, tts)
                                    .eat_many_comma_tail_end(
                    Pat::Unknow,
                    Parser::eat_pat,
                );
                Pat::DestructTuple{ name, elems: v }
            },
            tree!(loc, delim: Brace, mut tts) => {
                let ellipsis = match tts.last() {
                    Some(&sym!("..")) => true,
                    _ => false,
                };
                if ellipsis { tts.pop(); }
                let (v, _) = Parser::new_inner(loc, tts)
                                    .eat_many_comma_tail_end(
                    DestructField::Unknow,
                    Parser::eat_destruct_field,
                );
                Pat::DestructNormal{ name, fields: v, ellipsis }
            },
            _ => if let (false, 1, Some(&PathComp::Name{ name, hint: None })) =
                    (name.is_absolute, name.comps.len(), name.comps.first()) {
                let pat = match_eat!{ self.0;
                    sym!("@") => Some(Box::new(self.eat_pat())),
                    _ => None,
                };
                Pat::BindLike{ name, ref_: None, mut_: None, pat }
            } else {
                Pat::Path(name)
            },
        }
    }

    /// Eat and return a field of pattern on struct with fields.
    fn eat_destruct_field(&mut self) -> DestructField<'t> {
        let name = self.eat_ident();
        let pat = match_eat!{ self.0;
            sym!(":") => Some(Box::new(self.eat_pat())),
            _ => None,
        };
        DestructField::Field{ name, pat }
    }

    /// Eat and return a type. If `accect_traits`, it can accept
    /// `Tr1 + Tr2 + ..`.
    fn eat_ty(&mut self, accept_traits: bool) -> Ty<'t> {
        match_eat!{ self.0;
            ident!("_") => Ty::Hole,
            sym!("!") => Ty::Never,
            kw!("Self") => Ty::Self_,
            tree!(loc, delim: Paren, tts) => {
                let (mut v, tail) = Parser::new_inner(loc, tts)
                                           .eat_many_comma_tail_end(
                    Ty::Unknow,
                    |p| p.eat_ty(true),
                );
                if v.len() == 1 && !tail {
                    Ty::Paren(Box::new(v.pop().unwrap()))
                } else {
                    Ty::Tuple(v)
                }
            },
            tree!(loc, delim: Bracket, tts) => {
                let mut p = Parser::new_inner(loc, tts);
                let ty = Box::new(p.eat_ty(true));
                match_eat!{ p.0;
                    sym!(";") => {
                        let size = Box::new(p.eat_expr(false, true));
                        Ty::Array{ ty, size, unknow: p.rest() }
                    },
                    _ => Ty::Slice{ ty, unknow: p.rest() },
                }
            },
            sym!("&") => {
                let lt = match_eat!{ self.0;
                    lt!(lt) => Some(lt),
                    _ => None,
                };
                let mut_ = eatKw!(self.0; "mut");
                let ty = Box::new(self.eat_ty(false));
                Ty::Ref{ lt, mut_, ty }
            },
            sym!("*"), kw!("const") =>
                Ty::Ptr{ mut_: None, ty: Box::new(self.eat_ty(false)) },
            sym!("*"), kw!("mut", loc) =>
                Ty::Ptr{ mut_: Some(loc), ty: Box::new(self.eat_ty(false)) },
            kw!("fn") =>
                self.eat_func_ty(None, ABI::Normal),
            kw!("extern"), kw!("fn") =>
                self.eat_func_ty(None, ABI::Extern),
            kw!("extern"), lit_str!(abi, loc), kw!("fn") =>
                self.eat_func_ty(None, ABI::Specific{ loc, abi }),
            kw!("unsafe", lu), kw!("fn") =>
                self.eat_func_ty(Some(lu), ABI::Normal),
            kw!("unsafe", lu), kw!("extern"), kw!("fn") =>
                self.eat_func_ty(Some(lu), ABI::Extern),
            kw!("unsafe", lu), kw!("extern"), lit_str!(abi, loc), kw!("fn") =>
                self.eat_func_ty(Some(lu), ABI::Specific{ loc, abi }),
            _ => if accept_traits {
                let (mut v, tail) = self.eat_many_tail(
                    symbol_type!("+"),
                    |p| match p.0.peek(0) {
                        Some(&sym!("+")) => false,
                        _ => !p.is_ty_apply_begin()
                    },
                    TyApply::Unknow,
                    Parser::eat_ty_apply,
                );
                if v.len() == 1 && !tail {
                    Ty::Apply(Box::new(v.pop().unwrap()))
                } else {
                    Ty::Traits(v)
                }
            } else if self.is_ty_apply_begin() {
                Ty::Apply(Box::new(self.eat_ty_apply()))
            } else {
                Ty::Traits(vec![]) // indicates null
            },
        }
    }

    /// Return whether the next TT can be the begin of TyApply.
    fn is_ty_apply_begin(&self) -> bool {
        match self.0.peek(0) {
            Some(&sym!("::")) |
            Some(&ident!(_)) |
            Some(&kw!("Self")) => true,
            _ => false,
        }
    }

    /// Eat and return a simple type or angle applicated type. It always
    /// returns a `TyApply::Apply`.
    fn eat_opt_angle_ty_apply_args(&mut self) -> Option<Vec<TyApplyArg<'t>>> {
        match_eat!{ self.0;
            sym!("<") => {
                let (args, _) = self.eat_many_tail(
                    symbol_type!(","),
                    |p| p.try_eat_templ_end(),
                    TyApplyArg::Unknow,
                    Parser::eat_ty_apply_arg,
                );
                Some(args)
            },
            _ => None,
        }
    }


    fn eat_ty_apply(&mut self) -> TyApply<'t> {
        let name = self.eat_path();
        match_eat!{ self.0;
            tree!(loc, delim: Paren, tts) => {
                let (args, _) = Parser::new_inner(loc, tts)
                                       .eat_many_comma_tail_end(
                    Ty::Unknow,
                    |p| p.eat_ty(true),
                );
                let ret_ty = self.eat_opt_ret_ty();
                TyApply::Paren{ name, args, ret_ty }
            },
            _ => {
                let args = self.eat_opt_angle_ty_apply_args();
                TyApply::Angle{ name, args }
            },
        }
    }

    /// Eat and return an argument of parameterized generic type, one of the
    /// arguments inside angles of `T<'a, i32, K=i32>`.
    fn eat_ty_apply_arg(&mut self) -> TyApplyArg<'t> {
        match_eat!{ self.0;
            lt!(lt) => TyApplyArg::Lifetime(lt),
            sym!("=", loc) => {
                let ty = self.eat_ty(true);
                TyApplyArg::AssocTy{ name: Err(&loc[..0]), ty } // before `=`
            },
            ident!(name), sym!("=") => {
                let ty = self.eat_ty(true);
                TyApplyArg::AssocTy{ name: Ok(name), ty }
            },
            _ => TyApplyArg::Ty(self.eat_ty(true)),
        }
    }

    /// Eat the tail (after `fn`) and return a function type.
    fn eat_func_ty(&mut self, unsafe_: OptSym<'t>, abi: ABI<'t>) -> Ty<'t> {
        let (args, va) = match_eat!{ self.0;
            tree!(loc, delim: Paren, tts) => {
                let (args, va, _) = Parser::new_inner(loc, tts)
                                           .eat_many_tail_last(
                    symbol_type!(","),
                    |p| p.is_end(),
                    FuncTyParam::Unknow,
                    |p| match_eat!{ p.0;
                        sym!("...", loc) => Some(loc),
                        _ => None,
                    },
                    |p| match_eat!{ p.0;
                        ident!(name), sym!(":") =>
                            FuncTyParam::Param{ name: Some(Ok(name))
                                              , ty: p.eat_ty(true) },
                        _ => FuncTyParam::Param{ name: None
                                               , ty: p.eat_ty(true) },
                    },
                );
                (Some(args), va)
            },
            _ => (None, None),
        };
        let ret_ty = self.eat_opt_ret_ty();
        let fun_ty = FuncTy{
            unsafe_,
            abi,
            args,
            va,
            ret_ty,
        };
        Ty::Func(Box::new(fun_ty))
    }

    /// If the next TT can be the start of expression, eat and return the boxed
    /// expression. Otherwise, return None.
    fn eat_opt_boxed_expr(&mut self) -> Option<Box<Expr<'t>>> {
        if self.is_expr_begin() {
            Some(Box::new(self.eat_expr(false, true)))
        } else {
            None
        }
    }

    /// Eat and return an expression.
    /// If `item_like_first` is true and the following TTs can be an
    /// item-like-expr, it will return immediately without checking binary ops.
    /// Eg. `m!{} - 1` will be parsed into `m!{}` and `-1` will be remained.
    /// If `struct_expr` is false, it will not recognize struct expression
    /// `S [<T, ..>] { .. }`。
    /// Reference:
    /// http://doc.rust-lang.org/reference/expressions.html#operator-precedence
    fn eat_expr(
        &mut self,
        item_like_first: bool,
        struct_expr: bool,
    ) -> Expr<'t> {
        self.eat_expr_binop(item_like_first, struct_expr)
    }

    /// Eat the cast expression maybe with binary operators.
    /// See also: `Parser::eat_expr()`
    fn eat_expr_binop(
        &mut self,
        item_like_first: bool,
        struct_expr: bool,
    ) -> Expr<'t> {
        // TODO: should match over lots of operators
        #![cfg_attr(feature="clippy", allow(cyclomatic_complexity))]

        let e0 = |p: &mut Self| p.eat_expr_cast(item_like_first, struct_expr);
        let efst = e0(self);
        if item_like_first && efst.is_item_like() {
            return efst;
        }
        macro_rules! m {
            ([$($s:tt $lvl:tt $dt:tt $op:tt)*] $n:expr; @ $efst:expr) => {{
                fn reduce<'t>(
                    st_sym: &mut Vec<(BinaryOp, LocStr<'t>, i8)>,
                    st_expr: &mut Vec<Expr<'t>>,
                    lvl: i8,
                ) {
                    loop {
                        match st_sym.last() {
                            Some(&(op, op_loc, lvl_)) if lvl_ >= lvl => {
                                let r = Box::new(st_expr.pop().unwrap());
                                let l = Box::new(st_expr.pop().unwrap());
                                st_expr.push(
                                    Expr::BinaryOp{ op, op_loc, l, r }
                                );
                                st_sym.pop();
                            },
                            _ => break,
                        }
                    }
                }
                let mut st_sym: Vec<(BinaryOp, LocStr, i8)> = vec![];
                let mut st_expr = vec![$efst];
                loop {
                    match_eat!{ self.0;
                        $(sym!($s, loc) => {
                            reduce(&mut st_sym, &mut st_expr, $lvl + $dt);
                            st_sym.push((BinaryOp::$op, loc, $lvl));
                            st_expr.push(e0(self));
                        },)*
                        _ => break,
                    }
                }
                reduce(&mut st_sym, &mut st_expr, 0);
                assert_eq!(st_expr.len(), 1);
                st_expr.pop().unwrap()
            }};
            ([$($to:tt)*] $i:expr; L: $($s:tt ($op:ident)),*; $($ti:tt)*) => {
                m!([$($s $i 0 $op)* $($to)*] $i + 1; $($ti)*)
            };
            ([$($to:tt)*] $i:expr; R: $($s:tt ($op:ident)),*; $($ti:tt)*) => {
                m!([$($s $i 1 $op)* $($to)*] $i + 1; $($ti)*)
            };
            ($efst:expr; $($t:tt)*) => { m!([] 0; $($t)* @ $efst) };
        }
        m!{ efst;
            R: "="(Assign), "+="(AddAssign), "-="(SubAssign),
                "*="(MulAssign), "/="(DivAssign), "%="(ModAssign),
                "&="(AndAssign), "|="(OrAssign),
                "<<="(ShlAssign), ">>="(ShrAssign);
            R: "<-"(Place);
            L: ".."(Range), "..."(RangeInclusive);
            L: "||"(LogOr);
            L: "&&"(LogAnd);
            L: "=="(Equ), "!="(Ne),
                "<"(Lt), ">"(Gt), "<="(Le), ">="(Ge);
            L: "|"(Or);
            L: "^"(Xor);
            L: "&"(And);
            L: "<<"(Shl), ">>"(Shr);
            L: "+"(Add), "-"(Sub);
            L: "*"(Mul), "/"(Div);
        }
    }

    /// Eat the cast expression maybe with `as` or `:`.
    /// See also: `Parser::eat_expr()`
    fn eat_expr_cast(
        &mut self,
        item_like_first: bool,
        struct_expr: bool,
    ) -> Expr<'t> {
        let mut e = self.eat_expr_prefix(item_like_first, struct_expr);
        if !(e.is_item_like() && item_like_first) {
            loop {
                match_eat!{ self.0;
                    kw!("as", kw_loc) => e = Expr::As{
                        expr: Box::new(e),
                        kw_loc,
                        ty: Box::new(self.eat_ty(false)),
                    },
                    sym!(":", kw_loc) => e = Expr::Colon{
                        expr: Box::new(e),
                        kw_loc,
                        ty: Box::new(self.eat_ty(false)),
                    },
                    _ => break,
                }
            }
        }
        e
    }

    /// Eat the expression maybe with prefix operators.
    /// See also: `Parser::eat_expr()`
    fn eat_expr_prefix(
        &mut self,
        item_like_first: bool,
        struct_expr: bool,
    ) -> Expr<'t> {
        let op = match_eat!{ self.0;
            sym!("-", loc) => Some((UnaryOp::Neg, loc)),
            sym!("!", loc) => Some((UnaryOp::Not, loc)),
            sym!("&", loc), kw!("mut") => Some((UnaryOp::BorrowMut, loc)),
            sym!("&", loc) => Some((UnaryOp::Borrow, loc)),
            sym!("*", loc) => Some((UnaryOp::Deref, loc)),
            _ => None,
        };
        match op {
            Some((op, op_loc)) => Expr::UnaryOp {
                op,
                op_loc,
                expr: Box::new(self.eat_expr_prefix(false, struct_expr)),
            },
            None => self.eat_expr_postfix(item_like_first, struct_expr),
        }
    }

    /// Eat the expression maybe with postfix operators.
    /// See also: `Parser::eat_expr()`
    fn eat_expr_postfix(
        &mut self,
        item_like_first: bool,
        struct_expr: bool,
    ) -> Expr<'t> {
        let mut e = self.eat_expr_min(struct_expr);
        if e.is_item_like() && item_like_first {
            return e;
        }
        loop {
            match_eat!{ self.0;
                sym!("?", op_loc) =>
                    e = Expr::UnaryOp{
                        op: UnaryOp::Try,
                        op_loc,
                        expr: Box::new(e),
                    },
                sym!("."), lit_int!(index, ind_loc) =>
                    e = Expr::TupleField{ obj: Box::new(e), ind_loc, index },
                sym!(".") => {
                    let comp = self.eat_path_comp();
                    match_eat!{ self.0;
                        tree!(loc, delim: Paren, tts) => {
                            let (args, _) = Parser::new_inner(loc, tts)
                                                   .eat_many_comma_tail_end(
                                Expr::Unknow,
                                |p| p.eat_expr(false, true),
                            );
                            e = Expr::MemberCall{
                                obj: Box::new(e),
                                func: comp,
                                par_loc: &loc[..1], // `(`
                                args,
                            };
                        },
                        _ => e = Expr::StructField{
                            obj: Box::new(e),
                            field: comp,
                        },
                    }
                },
                tree!(loc, delim: Bracket, tts) => {
                    let mut p = Parser::new_inner(loc, tts);
                    let brk_loc = &loc[..1]; // `[`
                    let index = Box::new(p.eat_expr(false, true));
                    let unknow = p.rest();
                    e = Expr::Index{
                        obj: Box::new(e),
                        brk_loc,
                        index,
                        unknow,
                    };
                },
                tree!(loc, delim: Paren, tts) => {
                    let par_loc = &loc[..1]; // `(`
                    let (args, _) = Parser::new_inner(loc, tts).eat_many_comma_tail_end(
                        Expr::Unknow,
                        |p| p.eat_expr(false, true),
                    );
                    e = Expr::Call{ func: Box::new(e), par_loc, args };
                },
                _ => return e,
            }
        }
    }

    /// Eat and return a block expression, or return None.
    fn eat_opt_block_expr(&mut self) -> Option<Expr<'t>> {
        match_eat!{ self.0;
            tree!(loc, delim: Brace, tts) =>
                Some(Parser::new_inner(loc, tts).eat_block_expr_inner_end()),
            _ => None,
        }
    }

    /// Eat and return an expression element, like a literal or path. It never
    /// returns an expression of unary/binary operator.
    /// Warning: struct expression is an expression element, but (member)
    /// function call is not.
    /// If `struct_expr` is false, `S[<T>]{..}` will be cut and only `S` will
    /// be returned as a path.
    fn eat_expr_min(&mut self, struct_expr: bool) -> Expr<'t> {
        // TODO:
        #![cfg_attr(feature="clippy", allow(cyclomatic_complexity))]

        if let Some(p) = self.eat_opt_plugin_invoke() {
            return Expr::PluginInvoke(p);
        }
        match_eat!{ self.0;
            lit!(lit) => Expr::Literal(lit),
            tree!(loc, delim: Paren, tts) => {
                let (mut v, tail) = Parser::new_inner(loc, tts)
                                           .eat_many_comma_tail_end(
                    Expr::Unknow,
                    |p| p.eat_expr(false, true),
                );
                if v.len() == 1 && !tail {
                    Expr::Paren(Box::new(v.pop().unwrap()))
                } else {
                    Expr::Tuple(v)
                }
            },
            tree!(loc, delim: Bracket, tts) =>
                Parser::new_inner(loc, tts).eat_array_expr_inner_end(),
            tree!(loc, delim: Brace, tts) =>
                Parser::new_inner(loc, tts).eat_block_expr_inner_end(),
            kw!("unsafe") =>
                Expr::Unsafe(self.eat_opt_block_expr().map(Box::new)),
            sym!("|", loc) =>
                self.eat_lambda_expr_tail(None, loc, false),
            sym!("||", loc) =>
                self.eat_lambda_expr_tail(None, &loc[..1], true),
            kw!("move", lm), sym!("|", loc) =>
                self.eat_lambda_expr_tail(Some(lm), loc, false),
            kw!("move", lm), sym!("||", loc) =>
                self.eat_lambda_expr_tail(Some(lm), &loc[..1], true),
            kw!("break", kw_loc), lt!(lt) =>
                Expr::Break{ label: Some(lt)
                           , kw_loc
                           , expr: self.eat_opt_boxed_expr() },
            kw!("break", kw_loc) =>
                Expr::Break{ label: None
                           , kw_loc
                           , expr: self.eat_opt_boxed_expr() },
            kw!("continue", kw_loc), lt!(lt) =>
                Expr::Continue{ label: Some(lt), kw_loc },
            kw!("continue", kw_loc) =>
                Expr::Continue{ label: None, kw_loc },
            kw!("return", kw_loc) =>
                Expr::Return{ kw_loc, expr: self.eat_opt_boxed_expr() },
            lt!(lt), sym!(":"), kw!("loop") => self.eat_loop_tail(Some(lt)),
            kw!("loop") => self.eat_loop_tail(None),
            lt!(lt), sym!(":"), kw!("while") => self.eat_while_tail(Some(lt)),
            kw!("while") => self.eat_while_tail(None),
            lt!(lt), sym!(":"), kw!("for") => self.eat_for_tail(Some(lt)),
            kw!("for") => self.eat_for_tail(None),
            kw!("if") => self.eat_if_tail(),
            kw!("match", loc) => self.eat_match_tail(loc),
            _ => {
                let name = self.eat_path();
                let opt_struct = if struct_expr {
                    match_eat!{ self.0;
                        tree!(loc, delim: Brace, tts) => {
                            let (fields, base) =
                                Parser::new_inner(loc, tts)
                                       .eat_expr_struct_inner_end();
                            Some((Some(fields), base))
                        },
                        _ => None,
                    }
                } else { None };
                match opt_struct {
                    Some((fields, base)) => Expr::Struct{
                        ty: Box::new(Ty::from_path(name)),
                        fields,
                        base,
                    },
                    None => Expr::Path(name),
                }
            },
        }
    }

    /// Eat and return the loop expression after `loop`.
    fn eat_loop_tail(&mut self, label: Option<Lifetime<'t>>) -> Expr<'t> {
        let body = self.eat_opt_block_expr().map(Box::new);
        Expr::Loop{ label, body }
    }

    /// Eat and return the while expression after `while`.
    fn eat_while_tail(&mut self, label: Option<Lifetime<'t>>) -> Expr<'t> {
        match_eat!{ self.0;
            kw!("let") => {
                let pat = Box::new(self.eat_pat());
                let expr = match_eat!{ self.0;
                    sym!("=") => Some(Box::new(self.eat_expr(false, false))),
                    _ => None,
                };
                let body = self.eat_opt_block_expr().map(Box::new);
                Expr::WhileLet{ pat, expr, body }
            },
            _ => {
                let cond = Box::new(self.eat_expr(false, false));
                let body = self.eat_opt_block_expr().map(Box::new);
                Expr::While{ label, cond, body }
            },
        }
    }

    /// Eat and return the for expression after `for`.
    fn eat_for_tail(&mut self, label: Option<Lifetime<'t>>) -> Expr<'t> {
        let pat = Box::new(self.eat_pat());
        let iter = match_eat!{ self.0;
            kw!("in") => Some(Box::new(self.eat_expr(false, false))),
            _ => None,
        };
        let body = self.eat_opt_block_expr().map(Box::new);
        Expr::For{ label, pat, iter, body}
    }

    /// Eat and return the if expression after `if`.
    fn eat_if_tail(&mut self) -> Expr<'t> {
        let then_else = |p: &mut Self| {
            let then_expr = p.eat_opt_block_expr().map(Box::new);
            let else_expr = match_eat!{ p.0;
                kw!("else"), kw!("if") =>
                    Some(Some(Box::new(p.eat_if_tail()))),
                kw!("else") =>
                    Some(p.eat_opt_block_expr().map(Box::new)),
                _ => None,
            };
            (then_expr, else_expr)
        };
        match_eat!{ self.0;
            kw!("let") => {
                let pat = Box::new(self.eat_pat());
                let match_expr = match_eat!{ self.0;
                    sym!("=") => Some(Box::new(self.eat_expr(false, false))),
                    _ => None,
                };
                let (then_expr, else_expr) = then_else(self);
                Expr::IfLet{ pat, match_expr, then_expr, else_expr }
            },
            _ => {
                let cond = Box::new(self.eat_expr(false, false));
                let (then_expr, else_expr) = then_else(self);
                Expr::If{ cond, then_expr, else_expr }
            },
        }
    }

    /// Eat and return the match expression after `match`.
    fn eat_match_tail(&mut self, kw_loc: LocStr<'t>) -> Expr<'t> {
        let expr = Box::new(self.eat_expr(false, false));
        let arms = match_eat!{ self.0;
            tree!(loc, delim: Brace, tts) => {
                let (arms, _) = Parser::new_inner(loc, tts)
                                       .eat_many_comma_tail_end(
                    MatchArm::Unknow,
                    |p| {
                        let pats = p.eat_many_sep(
                            symbol_type!("|"),
                            |p| match p.0.peek(0) {
                                Some(&sym!("|")) => false,
                                _ => !p.is_pat_begin(),
                            },
                            Pat::Unknow,
                            Parser::eat_pat,
                        );
                        let cond = match_eat!{ p.0;
                            kw!("if") =>
                                Some(Box::new(p.eat_expr(false, true))),
                            _ => None,
                        };
                        let expr = match_eat!{ p.0;
                            sym!("=>") => Some(p.eat_expr(false, true)),
                            _ => None,
                        };
                        MatchArm::Arm{ pats, cond, expr }
                    },
                );
                Some(arms)
            },
            _ => None,
        };
        Expr::Match{ kw_loc, expr, arms }
    }

    /// Eat the inner of a block expression to the end, and return the block
    /// expression.
    fn eat_block_expr_inner_end(mut self) -> Expr<'t> {
        let mut stmts = vec![];
        let mut ret = None;
        while !self.is_end() {
            if let Some(expr) = ret.take() { // .. <expr> |;
                let semi = self.eat_semi();
                let stmt = match expr {
                    Expr::PluginInvoke(p) =>
                        Stmt::PluginInvoke{ p, semi },
                    _ => Stmt::Expr{ expr, semi },
                };
                stmts.push(stmt);
            } else if self.eat_semi().is_ok() { // .. <expr>; |;
                // NOP
            } else if self.is_item_begin() {
                stmts.push(Stmt::Item(Box::new(self.eat_item())));
            } else { match_eat!{ self.0;
                kw!("let") => {
                    let pat = self.eat_pat();
                    let ty = match_eat!{ self.0;
                        sym!(":") => Some(Box::new(self.eat_ty(true))),
                        _ => None,
                    };
                    let expr = match_eat!{ self.0;
                        sym!("=") =>
                            Some(Box::new(self.eat_expr(false, true))),
                        _ => None,
                    };
                    let semi = self.eat_semi();
                    stmts.push(Stmt::Let{ pat, ty, expr, semi });
                },
                _ => if self.is_expr_begin() {
                    ret = Some(self.eat_expr(true, true));
                } else {
                    match_eat!{ self.0;
                        tt => stmts.push(Stmt::Unknow(tt)),
                        _ => unreachable!(), // not `is_end()`
                    }
                },
            }}
        }
        Expr::Block{ stmts, ret: ret.map(Box::new) }
    }

    /// Eat the inner of a array literal or filled array to the end, and return
    /// the Expr::ArrayFill or Expr::ArrayLit.
    fn eat_array_expr_inner_end(mut self) -> Expr<'t> {
        let e0 = self.eat_expr(false, true);
        match_eat!{ self.0;
            sym!(";") => {
                let elem = Box::new(e0);
                let len = Box::new(self.eat_expr(false, true));
                Expr::ArrayFill{ elem, len, unknow: self.rest() }
            },
            _ => {
                match_eat!{ self.0;
                    sym!(",") => (),
                    _ => (),
                };
                let (mut elems, _) = self.eat_many_comma_tail_end(
                    Expr::Unknow,
                    |p| p.eat_expr(false, true),
                );
                elems.insert(0, e0);
                Expr::ArrayLit(elems)
            },
        }
    }

    /// If the next TT starts with `|`, eat `|` and return true. Otherwise,
    /// return false.
    fn try_eat_lambda_arg_end(&mut self) -> bool {
        match_eat!{ self.0;
            sym!("|") => true,
            sym!("||", loc) => { symBack!(self.0, "|", loc); true },
            sym!("|=", loc) => { symBack!(self.0, "=", loc); true },
            _ => false,
        }
    }

    /// Eat and return a lambda expression after `[move] |` or `[move] ||`.
    fn eat_lambda_expr_tail(
        &mut self,
        move_: OptSym<'t>,
        loc: LocStr<'t>,
        is_closed: bool,
    ) -> Expr<'t> {
        let args = if is_closed {
            vec![]
        } else {
            self.eat_many_tail(
                symbol_type!(","),
                Parser::try_eat_lambda_arg_end,
                FuncParam::Unknow,
                Parser::eat_lambda_param,
            ).0
        };
        let (ret_ty, body) = match_eat!{ self.0;
            sym!("->") => (
                Some(Box::new(self.eat_ty(true))),
                self.eat_opt_block_expr().map(Box::new),
            ),
            _ => (
                None,
                Some(Box::new(self.eat_expr(false, true))),
            ),
        };
        let sig = Box::new(LambdaSig{ move_, loc, args, ret_ty });
        Expr::Lambda{ sig, body }
    }

    /// Eat and return a parameter of lambda function.
    fn eat_lambda_param(&mut self) -> FuncParam<'t> {
        let pat = self.eat_pat();
        let ty = match_eat!{ self.0;
            sym!(":") => Some(Box::new(self.eat_ty(true))),
            _ => None,
        };
        FuncParam::Bind{ pat, ty }
    }

    /// Eat the content inside the brace of struct expression `S{ .. }` to the
    /// end.
    fn eat_expr_struct_inner_end(
        &mut self,
    ) -> (Vec<ExprStructField<'t>>, Option<Box<Expr<'t>>>) {
        let (v, base, _) = self.eat_many_tail_last(
            symbol_type!(","),
            |p| p.is_end(),
            ExprStructField::Unknow,
            |p| match_eat!{ p.0;
                sym!("..") => Some(Box::new(p.eat_expr(false, true))),
                _ => None,
            },
            |p| {
                let name = p.eat_ident();
                let expr = match_eat!{ p.0;
                    sym!(":") => Some(Box::new(p.eat_expr(false, true))),
                    _ => None,
                };
                ExprStructField::Field{ name, expr }
            },
        );
        (v, base)
    }

    /// Eat and return an plugin invoke, or return None.
    fn eat_opt_plugin_invoke(&mut self) -> Option<PluginInvoke<'t>> {
        match_eat!{ self.0;
            ident!(name), sym!("!") => {
                let ident = match_eat!{ self.0;
                    ident!(s) => Some(Ok(s)),
                    _ => None,
                };
                let tt = match_eat!{ self.0;
                    t@tree!(_, ..) => Some(t),
                    _ => None,
                };
                Some(PluginInvoke{ name: Ok(name), ident, tt })
            },
            _ => None,
        }
    }
}
