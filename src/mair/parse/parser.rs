use super::lexer::{TokenKind as Tokk, SymbolType, Token};
use super::ast::*;
use super::error::{UnmatchedDelimError, HardSyntaxError};
use super::ttstream::TTStream;
use self::Delimiter::*;

pub struct Parser<'t, 'e> where 't: 'e {
    tts:  TTStream<'t>,
    errs: &'e mut Vec<HardSyntaxError<'t>>,
}

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
pub fn parse_crate<'t>(
    source: &'t str,
    tts: Vec<TT<'t>>,
) -> (Mod<'t>, Vec<HardSyntaxError<'t>>) {
    let mut errs = vec![];
    let m = Parser::new(source, tts, &mut errs).eat_mod_end();
    (m, errs)
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
        kw!($kw) => true,
        _ => false,
    }}
}

impl<'t, 'e> Parser<'t, 'e> {
    pub fn new(
        source: &'t str,
        tts:    Vec<TT<'t>>,
        errs:   &'e mut Vec<HardSyntaxError<'t>>,
    ) -> Self {
        Parser {
            tts: TTStream::new(tts, &source[..0]),
            errs,
        }
    }

    fn new_inner<'a>(
        &'a mut self,
        loc: LocStr<'t>,
        tts: Vec<TT<'t>>,
    ) -> Parser<'t, 'a> {
        Parser {
            tts:  TTStream::new(tts, &loc[1..1]), // skip the first `(`
            errs: self.errs,
        }
    }

    /// Emit an error in `loc` with `reason`.
    fn err(&mut self, loc: &'t str, reason: &'static str) {
        self.errs.push(HardSyntaxError{ loc, reason })
    }

    /// Return whether there's no TT left.
    pub fn is_end(&self) -> bool {
        self.tts.peek(0).is_none()
    }

    /// Return an empty LocStr pointing at the end of previous TT (is any),
    /// or the beginning of source file.
    fn prev_pos(&self) -> LocStr<'t> {
        self.tts.prev_last_pos()
    }

    /// Emit an error at `self.prev_pos()` with `reason`.
    fn err_prev(&mut self, reason: &'static str) {
        let loc = self.prev_pos();
        self.err(loc, reason);
    }

    /// Expect the end of TTs. Any TT left will be marked as error.
    fn expect_end(&mut self) {
        let mut locs = vec![];
        for (_, loc) in &mut self.tts {
            locs.push(loc);
        }
        for loc in locs {
            self.err(loc, "Expect nothing");
        }
    }

    /// Eat and return a semicolon.
    fn expect_semi(&mut self) {
        match_eat!{ self.tts;
            sym!(";") => (),
            _ => self.err_prev("Expect a semicolon"),
        }
    }

    /// Eat `(<elem> <sep>)* <elem>? <end>`, return (`elem`s, whether the TT
    /// before `end` is `sep`).
    fn eat_many_sep_tail<T, F, G>(
        &mut self,
        sep:  SymbolType,
        elem: F,
        end:  G,
    ) -> (Vec<T>, bool)
    where F: Fn(&mut Self) -> T,
          G: Fn(&mut Self) -> bool {
        let mut v = vec![];
        'elem: while !end(self) {
            v.push(elem(self));
            while !end(self) {
                let is_sep = match self.tts.peek(0) {
                    Some(&tok!(Tokk::Symbol(s))) if s == sep => true,
                    _ => false,
                };
                if is_sep {
                    self.tts.next().unwrap(); // is `sep`
                    continue 'elem;
                } else {
                    match_eat!{ self.tts;
                        tok!(_, loc) => self.err(loc, "Expect a separator"),
                        _ => unreachable!(), // not `end()`
                    }
                }
            }
            return (v, false); // `end` without eating `sep`
        }
        (v, true)
    }

    /// Eat `(<elem> `,`)* (<elem> | <last>)? <end>`, return (`elem`s, the
    /// optional `last`).
    fn eat_many_comma_tail_last<T, U, F, G, H>(
        &mut self,
        elem: F,
        last: G,
        end:  H,
    ) -> (Vec<T>, Option<U>)
    where F: Fn(&mut Self) -> T,
          G: Fn(&mut Self) -> Option<U>,
          H: Fn(&mut Self) -> bool {
        let mut v = vec![];
        'elem: while !end(self) {
            if let Some(x) = last(self) {
                return (v, Some(x));
            }
            v.push(elem(self));
            while !end(self) { // until eating a `,` or reach the `end`
                match_eat!{ self.tts;
                    sym!(",") => continue 'elem,
                    tok!(_, loc) => self.err(loc, "Expect `,`"),
                    _ => unreachable!(), // not `end`
                }
            }
            break; // `end` without `,`
        }
        (v, None)
    }

    /// Eat `(<elem> `,`)* <elem>`, return `elem`s.
    fn eat_many_sep<T, F, G>(
        &mut self,
        sep:     SymbolType,
        no_elem: &'static str,
        elem:    F,
        end:     G,
    ) -> Vec<T>
    where F: Fn(&mut Self) -> T,
          G: Fn(&mut Self) -> bool {
        let (v, tail) = self.eat_many_sep_tail(sep, elem, end);
        if tail {
            self.err_prev(no_elem);
        }
        v
    }

    /// Eat `(<elem> `,`)* <elem>? <EOF>`, return (`elem`s, whether the last
    /// TT is `,`)
    fn eat_many_comma_tail_end<T, F>(
        mut self,
        elem: F,
    ) -> (Vec<T>, bool)
    where F: Fn(&mut Self) -> T {
        let (v, tail) = self.eat_many_sep_tail(
            symbol_type!(","),
            elem,
            |p| p.is_end(),
        );
        self.expect_end();
        (v, tail)
    }

    /// Return whether the next TT can be the start of an item.
    fn is_item_begin(&self) -> bool {
        match self.tts.peek(0) {
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
            Some(&kw!("unsafe")) => match self.tts.peek(1) {
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
        match self.tts.peek(0) {
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
        match self.tts.peek(0) {
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

    /// Eat inner attributes and `f`s until the end.
    fn eat_mod_like_end<T, F>(
        &mut self,
        attrs: &mut Vec<Attr<'t>>,
        f:     F,
    ) -> Vec<T>
    where F: Fn(&mut Self) -> Option<T> {
        attrs.append(&mut self.eat_inner_attrs());
        let mut v = vec![];
        while !self.is_end() {
            if let Some(x) = f(self) {
                v.push(x);
            }
        }
        v
    }

    /// Eat inner attributes and then items to the end.
    pub fn eat_mod_end(mut self) -> Mod<'t> {
        let mut attrs = vec![];
        let items = self.eat_mod_like_end(&mut attrs, |p| p.eat_item());
        Mod{ attrs, items }
    }

    /// Eat and return inner attributes and items inside `{}`, or return None.
    fn eat_opt_brace_mod(&mut self) -> Option<Mod<'t>> {
        match_eat!{ self.tts;
            tree!(loc, delim: Brace, tts) =>
                Some(self.new_inner(loc, tts).eat_mod_end()),
            _ => None,
        }
    }

    /// Eat and return an identifier, or return the empty str slice after the
    /// last TT.
    fn eat_ident(&mut self) -> Ident<'t> {
        match_eat!{ self.tts;
            ident!(s) => Ok(s),
            _ => Err(self.prev_pos()),
        }
    }

    /// Eat and return a Path.
    fn eat_path(&mut self) -> Path<'t> {
        let is_absolute = match_eat!{ self.tts;
            sym!("::") => true,
            _ => false,
        };
        let mut comps = vec![self.eat_path_comp()];
        loop {
            match_eat!{ self.tts;
                sym!("::") => comps.push(self.eat_path_comp()),
                _ => break,
            }
        }
        Path{ is_absolute, comps }
    }

    /// Eat and return a path component.
    fn eat_path_comp(&mut self) -> PathComp<'t> {
        match_eat!{ self.tts;
            kw!("self", loc) => PathComp::Self_(loc),
            kw!("Self", loc) => PathComp::SelfTy_(loc),
            kw!("super", loc) => PathComp::Super(loc),
            _ => {
                let name = self.eat_ident();
                let hint = match_eat!{ self.tts;
                    sym!("::"), sym!("<") => {
                        let (v, _) = self.eat_many_sep_tail(
                            symbol_type!(","),
                            |p| match_eat!{ p.tts;
                                lt!(lt) => TyHintArg::Lifetime(lt),
                                _ => TyHintArg::Ty(p.eat_ty(true)),
                            },
                            Parser::try_eat_templ_end,
                        );
                        Some(v)
                    },
                    _ => None,
                };
                PathComp::Name{ name, hint }
            },
        }
    }

    /// Eat inner attributes as more as possible.
    fn eat_inner_attrs(&mut self) -> Vec<Attr<'t>> {
        let mut v = vec![];
        loop {
            match_eat!{ self.tts;
                tok!(Tokk::InnerDoc(doc), loc) =>
                    v.push(Attr::Doc{ loc, doc }),
                sym!("#"), sym!("!"), tree!(loc, delim: Bracket, tts) => {
                    let mut p = self.new_inner(loc, tts);
                    let meta = p.eat_meta();
                    p.expect_end();
                    v.push(Attr::Meta(meta))
                },
                _ => return v,
            }
        }
    }

    /// Eat outer attributes as more as possible.
    fn eat_outer_attrs(&mut self) -> Vec<Attr<'t>> {
        let mut v = vec![];
        loop {
            match_eat!{ self.tts;
                tok!(Tokk::OuterDoc(doc), loc) =>
                    v.push(Attr::Doc{ loc, doc }),
                sym!("#"), tree!(loc, delim: Bracket, tts) => {
                    let mut p = self.new_inner(loc, tts);
                    let meta = p.eat_meta();
                    p.expect_end();
                    v.push(Attr::Meta(meta))
                },
                _ => return v,
            }
        }
    }

    /// Eat a valid meta.
    fn eat_meta(&mut self) -> Meta<'t> {
        let name = self.eat_ident();
        match_eat!{ self.tts;
            sym!("="), lit!(value) =>
                Meta::KeyValue{ key: name, value },
            tree!(loc, delim: Paren, tts) => {
                let (subs, _) = self.new_inner(loc, tts)
                                    .eat_many_comma_tail_end(
                    |p| p.eat_meta(),
                );
                Meta::Sub{ name, subs }
            },
            _ => Meta::Flag(name),
        }
    }

    /// Eat an item. It will consume at lease one TT.
    /// Warning: There must be at least one TT left.
    fn eat_item(&mut self) -> Option<Item<'t>> {
        let mut attrs = self.eat_outer_attrs();
        let is_pub = eatKw!(self.tts; "pub");
        let opt_detail = self.eat_opt_item_detail(&mut attrs);
        let detail = match opt_detail {
            Some(x) => x,
            None if attrs.is_empty() && !is_pub => {
                // havn't consumed `pub`
                // "consumes nothing and nothing left" is impossible.
                let (_, loc) = self.tts.next().unwrap(); // here <-/
                self.err(loc, "Unknow beginning of item");
                return None
            },
            None => return None,
        };
        Some(Item{ attrs, is_pub, detail })
    }

    /// Eat and return the detail of an item, or return None.
    fn eat_opt_item_detail(
        &mut self,
        attrs: &mut Vec<Attr<'t>>,
    ) -> Option<ItemKind<'t>> {
        if let Some(p) = self.eat_opt_plugin_invoke() {
            return Some(ItemKind::PluginInvoke(p));
        }
        match_eat!{ self.tts;
            kw!("extern"), kw!("crate") => Some(self.eat_extern_crate_tail()),
            kw!("use") => Some(self.eat_use_tail()),
            kw!("mod") => Some(self.eat_mod_tail(attrs)),
            kw!("fn") =>
                Some(self.eat_fn_tail(attrs, false, ABI::Normal)),
            kw!("extern"), kw!("fn") =>
                Some(self.eat_fn_tail(attrs, false, ABI::Extern)),
            kw!("extern"), lit_str!(abi, loc), kw!("fn") =>
                Some(self.eat_fn_tail(attrs, false, ABI::Specific{ loc, abi })),
            kw!("unsafe"), kw!("fn") =>
                Some(self.eat_fn_tail(attrs, true, ABI::Normal)),
            kw!("unsafe"), kw!("extern"), kw!("fn") =>
                Some(self.eat_fn_tail(attrs, true, ABI::Extern)),
            kw!("unsafe"), kw!("extern"), lit_str!(abi, loc), kw!("fn") =>
                Some(self.eat_fn_tail(attrs, true, ABI::Specific{ loc
                                                                    , abi })),
            kw!("extern") => Some(self.eat_extern_tail(attrs)),
            kw!("type")   => Some(self.eat_type_tail()),
            kw!("struct") => Some(self.eat_struct_tail()),
            kw!("enum")   => Some(self.eat_enum_tail()),
            kw!("const")  => Some(self.eat_const_static_tail(false)),
            kw!("static") => Some(self.eat_const_static_tail(true)),
            kw!("trait")  => Some(self.eat_trait_tail()),
            kw!("impl")   => Some(self.eat_impl_tail(attrs)),
            _ => None,
        }
    }

    /// Eat the tail after `extern crate`.
    fn eat_extern_crate_tail(&mut self) -> ItemKind<'t> {
        let name = self.eat_ident();
        self.expect_semi();
        ItemKind::ExternCrate{ name }
    }

    /// Eat the tail after `use`.
    fn eat_use_tail(&mut self) -> ItemKind<'t> {
        let supers = match_eat!{ self.tts;
            kw!("self"), sym!("::") => Some(0),
            kw!("super"), sym!("::") => {
                let mut n = 1;
                loop {
                    match_eat!{ self.tts;
                        kw!("super"), sym!("::") => n += 1,
                        _ => break,
                    }
                }
                Some(n)
            },
            sym!("::") => None,
            _ => None,
        };
        let mut comps = vec![];
        loop {
            match_eat!{ self.tts;
                ident!(name), sym!("::") =>
                    comps.push(Ok(name)),
                sym!("::") => {
                    let loc = self.prev_pos();
                    comps.push(Err(loc))
                },
                _ => break,
            }
        }
        let use_path = match supers {
            Some(supers) => UsePath::Relative{ supers, comps },
            None         => UsePath::Absolute{ comps },
        };
        self.eat_use_names_tail(use_path)
    }

    /// Eat the using names and semicolon in item `use`, return the ItemKind.
    fn eat_use_names_tail(&mut self, path: UsePath<'t>) -> ItemKind<'t> {
        match_eat!{ self.tts;
            sym!("*") => {
                self.expect_semi();
                ItemKind::UseAll{ path }
            },
            tree!(loc, delim: Brace, tts) => {
                let (names, _) = self.new_inner(loc, tts)
                                     .eat_many_comma_tail_end(
                    Parser::eat_use_name,
                );
                self.expect_semi();
                ItemKind::UseSome{ path, names }
            },
            _ => {
                let name = self.eat_use_name();
                self.expect_semi();
                ItemKind::UseOne{ path, name }
            },
        }
    }

    /// Eat and return a UseName like `self` or `name [as alias]`.
    fn eat_use_name(&mut self) -> UseName<'t> {
        match_eat!{ self.tts;
            kw!("self", loc) => UseName::Self_(loc),
            _ => {
                let name = self.eat_ident();
                let alias = match_eat!{ self.tts;
                    kw!("as") => Some(self.eat_ident()),
                    _ => None,
                };
                UseName::Name{ name, alias }
            },
        }
    }

    /// Eat the tail after `mod`.
    fn eat_mod_tail(&mut self, attrs: &mut Vec<Attr<'t>>) -> ItemKind<'t> {
        let name = self.eat_ident();
        match self.eat_opt_brace_mod() {
            Some(Mod{ attrs: mut inner_attrs, items }) => {
                attrs.append(&mut inner_attrs);
                ItemKind::Mod{ name, items }
            },
            None => {
                self.expect_semi();
                ItemKind::ExternMod{ name }
            },
        }
    }

    /// Eat the tail after `[unsafe] [extern [<abt>]] fn`.
    fn eat_fn_tail(
        &mut self,
        attrs:     &mut Vec<Attr<'t>>,
        is_unsafe: bool,
        abi:       ABI<'t>,
    ) -> ItemKind<'t> {
        let sig = Box::new(self.eat_fn_sig(is_unsafe, abi));
        match self.eat_block_expr() {
            Expr::Block{ attrs: mut inner_attrs, stmts, ret } => {
                attrs.append(&mut inner_attrs);
                let block = Expr::Block{ attrs: vec![], stmts, ret };
                ItemKind::Func{ sig, body: Box::new(block) }
            },
            Expr::Error => {
                self.expect_semi();
                ItemKind::FuncDecl{ sig }
            },
            _ => unreachable!(),
        }
    }

    /// Eat the parameter list including parens. Return (parameters, the
    /// location of optional `...`). If the next TT is not tree delimited by
    /// parens, it will emit an error.
    fn eat_param_list_end(
        &mut self,
    ) -> (Vec<FuncParam<'t>>, bool) {
        match_eat!{ self.tts;
            tree!(loc, delim: Paren, tts) => {
                let (args, va_) = self.new_inner(loc, tts)
                                     .eat_many_comma_tail_last(
                    Parser::eat_func_param,
                    |p| match_eat!{ p.tts;
                        sym!("...") => Some(()),
                        _ => None,
                    },
                    |p| p.is_end(),
                );
                (args, va_.is_some())
            },
            _ => {
                self.err_prev("Expect the parameter list");
                (vec![], false)
            },
        }
    }

    /// Eat and return the signature of a function.
    fn eat_fn_sig(
        &mut self,
        is_unsafe: bool,
        abi:       ABI<'t>,
    ) -> FuncSig<'t> {
        let name = self.eat_ident();
        let templ = self.eat_templ();
        let (args, is_va) = self.eat_param_list_end();
        let ret_ty = self.eat_opt_ret_ty();
        let whs = self.eat_opt_whs();
        FuncSig{ is_unsafe, abi, name, templ, args, is_va, ret_ty, whs }
    }

    /// Eat and return a parameter of function.
    fn eat_func_param(&mut self) -> FuncParam<'t> {
        match_eat!{ self.tts;
            sym!("&"), kw!("mut"), kw!("self") =>
                FuncParam::SelfRef{ is_mut: true },
            sym!("&"), kw!("self") =>
                FuncParam::SelfRef{ is_mut: false },
            kw!("self"), sym!(":") =>
                FuncParam::SelfAs(self.eat_ty(true)),
            kw!("mut"), kw!("self") =>
                FuncParam::SelfMove{ is_mut: true },
            kw!("self") =>
                FuncParam::SelfMove{ is_mut: false },
            _ => {
                let pat = self.eat_pat();
                let ty = match_eat!{ self.tts;
                    sym!(":") => self.eat_ty(true),
                    _ => {
                        self.err_prev("Expect a type annotation");
                        Ty::Error
                    },
                };
                FuncParam::Bind{ pat, ty: Box::new(ty) }
            },
        }
    }

    /// Eat the return type if the next TT is `->`, or return None.
    fn eat_opt_ret_ty(&mut self) -> Option<Box<Ty<'t>>> {
        match_eat!{ self.tts;
            sym!("->") => Some(Box::new(self.eat_ty(true))),
            _ => None,
        }
    }

    /// Eat the tail after `extern` (item `extern`).
    fn eat_extern_tail(&mut self, attrs: &mut Vec<Attr<'t>>) -> ItemKind<'t> {
        let abi = match_eat!{ self.tts;
            lit_str!(abi, loc) => ABI::Specific{ loc, abi },
            _ => ABI::Extern,
        };
        let items = match_eat!{ self.tts;
            tree!(loc, delim: Brace, tts) => {
                self.new_inner(loc, tts)
                    .eat_mod_like_end(
                        attrs,
                        |p| p.eat_extern_item(),
                    )
            },
            _ => {
                self.err_prev("Expect the body in `{}`");
                vec![]
            },
        };
        ItemKind::Extern{ abi, items }
    }

    /// Eat and return an item inside `extern` block. It will consume at least
    /// one TT.
    ///
    /// Warning: Never call it when `is_end()`.
    fn eat_extern_item(&mut self) -> Option<ExternItem<'t>> {
        let attrs = self.eat_outer_attrs();
        let is_pub = eatKw!(self.tts; "pub");
        match_eat!{ self.tts;
            kw!("fn") => {
                let name = self.eat_ident();
                let (args, is_va) = self.eat_param_list_end();
                let ret_ty = self.eat_opt_ret_ty();
                self.expect_semi();
                let detail = ExternItemKind::Func{ name, args, is_va, ret_ty };
                Some(ItemWrap{ attrs, is_pub, detail })
            },
            kw!("static") => {
                let name = self.eat_ident();
                let ty = match_eat!{ self.tts;
                    sym!(":") => Some(Box::new(self.eat_ty(true))),
                    _ => None,
                };
                self.expect_semi();
                let detail = ExternItemKind::Static{ name, ty };
                Some(ItemWrap{ attrs, is_pub, detail })
            },
            tok!(_, loc) => {
                self.err(loc, "Expect `fn` or `static`");
                None
            },
            _ => unreachable!(), // not `is_end`
        }
    }

    /// Eat the tail after `type`.
    fn eat_type_tail(&mut self) -> ItemKind<'t> {
        let alias = self.eat_ident();
        let templ = self.eat_templ();
        let whs = self.eat_opt_whs();
        let origin = match_eat!{ self.tts;
            sym!("=") => self.eat_ty(true),
            _ => {
                self.err_prev("Expect `= <type>`");
                Ty::Error
            },
        };
        self.expect_semi();
        ItemKind::Type{ alias, templ, whs, origin: Box::new(origin) }
    }

    /// Eat the tail after `struct`.
    fn eat_struct_tail(&mut self) -> ItemKind<'t> {
        let name = self.eat_ident();
        let templ = self.eat_templ();
        match_eat!{ self.tts;
            tree!(loc, delim: Paren, tts) => {
                let (elems, _) = self.new_inner(loc, tts)
                                     .eat_many_comma_tail_end(
                    Parser::eat_struct_tuple_elem,
                );
                let whs = self.eat_opt_whs();
                self.expect_semi();
                ItemKind::StructTuple{ name, templ, elems, whs }
            },
            _ => {
                let whs = self.eat_opt_whs();
                let opt_fields = match_eat!{ self.tts;
                    tree!(loc, delim: Brace, tts) => {
                        let (v, _) = self.new_inner(loc, tts)
                                         .eat_many_comma_tail_end(
                            Parser::eat_struct_field,
                        );
                        Some(v)
                    },
                    _ => None,
                };
                if let Some(fields) = opt_fields {
                    ItemKind::StructFields{ name, templ, whs, fields }
                } else {
                    self.expect_semi();
                    ItemKind::StructUnit{ name, templ, whs }
                }
            },
        }
    }

    /// Eat and return an element of tuple-like-struct.
    fn eat_struct_tuple_elem(&mut self) -> StructTupleElem<'t> {
        let attrs = self.eat_outer_attrs();
        let is_pub = eatKw!(self.tts; "pub");
        let ty = self.eat_ty(true);
        StructTupleElem{ attrs, is_pub, ty }
    }

    /// Eat and return a field of struct with fields.
    fn eat_struct_field(&mut self) -> StructField<'t> {
        let attrs = self.eat_outer_attrs();
        let is_pub = eatKw!(self.tts; "pub");
        let name = self.eat_ident();
        let ty = match_eat!{ self.tts;
            sym!(":") => self.eat_ty(true),
            _ => {
                self.err_prev("Expect `: <type>`");
                Ty::Error
            },
        };
        StructField{ attrs, is_pub, name, ty }
    }

    /// Eat the tail after `enum`.
    fn eat_enum_tail(&mut self) -> ItemKind<'t> {
        let name = self.eat_ident();
        let templ = self.eat_templ();
        let whs = self.eat_opt_whs();
        let vars = match_eat!{ self.tts;
            tree!(loc, delim: Brace, tts) => {
                let (v, _) = self.new_inner(loc, tts)
                                 .eat_many_comma_tail_end(
                    Parser::eat_enum_var,
                );
                v
            },
            _ => {
                self.err_prev("Expect the enum body `{}`");
                vec![]
            },
        };
        ItemKind::Enum{ name, templ, whs, vars }
    }

    /// Eat a variant of `enum`.
    fn eat_enum_var(&mut self) -> EnumVar<'t> {
        let attrs = self.eat_outer_attrs();
        let name = self.eat_ident();
        match_eat!{ self.tts;
            tree!(loc, delim: Paren, tts) => {
                let (elems, _) = self.new_inner(loc, tts)
                                     .eat_many_comma_tail_end(
                    Parser::eat_struct_tuple_elem,
                );
                EnumVar::Tuple{ attrs, name, elems }
            },
            tree!(loc, delim: Brace, tts) => {
                let (fields, _) = self.new_inner(loc, tts)
                                      .eat_many_comma_tail_end(
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
        let ty = match_eat!{ self.tts;
            sym!(":") => Box::new(self.eat_ty(true)),
            _ => {
                self.err_prev("Expect `: <type>`");
                Box::new(Ty::Error)
            },
        };
        let val = match_eat!{ self.tts;
            sym!("=") => Box::new(self.eat_expr(false, true)),
            _ => {
                self.err_prev("Expect `= <expr>`");
                Box::new(Expr::Error)
            },
        };
        self.expect_semi();
        if is_static {
            ItemKind::Static{ name, ty, val }
        } else {
            ItemKind::Const{ name, ty, val }
        }
    }

    /// Eat the tail after `trait`.
    fn eat_trait_tail(&mut self) -> ItemKind<'t> {
        let name = self.eat_ident();
        let templ = self.eat_templ();
        let base = match_eat!{ self.tts;
            sym!(":") => Some(Box::new(self.eat_ty(true))),
            _ => None,
        };
        let whs = self.eat_opt_whs();
        let items = match_eat!{ self.tts;
            tree!(loc, delim: Brace, tts) => {
                let mut items = vec![];
                let mut p = self.new_inner(loc, tts);
                while !p.is_end() {
                    if let Some(x) = p.eat_trait_item() {
                        items.push(x);
                    }
                }
                items
            },
            _ => {
                self.err_prev("Expect the body in `{}`");
                vec![]
            },
        };
        ItemKind::Trait{ name, templ, base, whs, items }
    }

    /// Eat `fn` item like `[unsafe] [extern [<abi>]] fn ...`. Return None if
    /// fails.
    fn eat_fn_item(
        &mut self,
        attrs: &mut Vec<Attr<'t>>,
    ) -> Option<ItemKind<'t>> {
        match_eat!{ self.tts;
            kw!("fn") =>
                Some(self.eat_fn_tail(attrs, false, ABI::Normal)),
            kw!("extern"), kw!("fn") =>
                Some(self.eat_fn_tail(attrs, false, ABI::Extern)),
            kw!("extern"), lit_str!(abi, loc), kw!("fn") =>
                Some(self.eat_fn_tail(attrs,
                                      false,
                                      ABI::Specific{ loc, abi })),
            kw!("unsafe"), kw!("fn") =>
                Some(self.eat_fn_tail(attrs, true, ABI::Normal)),
            kw!("unsafe"), kw!("extern"), kw!("fn") =>
                Some(self.eat_fn_tail(attrs, true, ABI::Extern)),
            kw!("unsafe"), kw!("extern"), lit_str!(abi, loc), kw!("fn") =>
                Some(self.eat_fn_tail(attrs,
                                      true,
                                      ABI::Specific{ loc, abi })),
            _ => None,
        }
    }

    /// Eat and return an item inside `trait` block. It will consume at least
    /// one TT.
    ///
    /// Warning: Never call it when `is_end()`.
    fn eat_trait_item(&mut self) -> Option<TraitItem<'t>> {
        let mut attrs = self.eat_outer_attrs();
        let is_pub = eatKw!(self.tts; "pub");
        match_eat!{ self.tts;
            kw!("type") => {
                let name = self.eat_ident();
                let default = match_eat!{ self.tts;
                    sym!("=") => Some(Box::new(self.eat_ty(true))),
                    _ => None,
                };
                self.expect_semi();
                let detail = TraitItemKind::AssocTy{ name, default };
                Some(ItemWrap{ attrs, is_pub, detail })
            },
            _ => {
                match self.eat_fn_item(&mut attrs) {
                    None => match_eat!{ self.tts;
                        tok!(_, loc) => {
                            self.err(loc, "Expect a `type` or `fn` item`");
                            None
                        },
                        _ => unreachable!(), // not `is_end`
                    },
                    Some(ItemKind::Func{ sig, body }) => {
                        let detail = TraitItemKind::Func{
                            sig,
                            default: Some(body),
                        };
                        Some(ItemWrap{ attrs, is_pub, detail })
                    },
                    Some(ItemKind::FuncDecl{ sig }) => {
                        let detail = TraitItemKind::Func{ sig, default: None };
                        Some(ItemWrap{ attrs, is_pub, detail })
                    },
                    Some(_) => unreachable!(), // eat_fn_tail() never return
                                               // others
                }
            },
        }
    }

    /// Eat the tail after `impl`.
    fn eat_impl_tail(&mut self, attrs: &mut Vec<Attr<'t>>) -> ItemKind<'t> {
        let templ = self.eat_templ();
        let ty = Box::new(self.eat_ty(true));
        let mut block = |p: &mut Self| match_eat!{ p.tts;
            tree!(loc, delim: Brace, tts) =>
                p.new_inner(loc, tts).eat_mod_like_end(
                    attrs,
                    |q| q.eat_impl_item(),
                ),
            _ => {
                p.err_prev("Expect the body in `{}`");
                vec![]
            },
        };
        match_eat!{ self.tts;
            kw!("for") => {
                let tr = ty;
                let ty = Box::new(self.eat_ty(true));
                let whs = self.eat_opt_whs();
                ItemKind::ImplTrait{ templ, tr, ty, whs, items: block(self) }
            },
            _ => {
                let whs = self.eat_opt_whs();
                ItemKind::ImplType{ templ, ty, whs, items: block(self) }
            },
        }
    }

    /// Eat and return an item inside `impl` block. It will consume at least
    /// one TT.
    ///
    /// Warning: Never call it when `is_end()`.
    fn eat_impl_item(&mut self) -> Option<ImplItem<'t>> {
        let mut attrs = self.eat_outer_attrs();
        let is_pub = eatKw!(self.tts; "pub");
        match_eat!{ self.tts;
            kw!("type") => {
                let name = self.eat_ident();
                let val = match_eat!{ self.tts;
                    sym!("=") => self.eat_ty(true),
                    _ => {
                        self.err_prev("Expect `= <type>`");
                        Ty::Error
                    },
                };
                self.expect_semi();
                let detail = ImplItemKind::AssocTy{ name, val: Box::new(val) };
                Some(ItemWrap{ attrs, is_pub, detail })
            },
            _ => {
                match self.eat_fn_item(&mut attrs) {
                    None => match_eat!{ self.tts;
                        tok!(_, loc) => {
                            self.err(loc, "Expect a `type` or `fn` item`");
                            None
                        },
                        _ => unreachable!(), // not `is_end`
                    },
                    Some(ItemKind::Func{ sig, body }) => {
                        let detail = ImplItemKind::Func{
                            sig,
                            body,
                        };
                        Some(ItemWrap{ attrs, is_pub, detail })
                    },
                    Some(ItemKind::FuncDecl{ sig }) => {
                        self.err_prev("Expect the function body");
                        let body = Box::new(Expr::Error);
                        let detail = ImplItemKind::Func{ sig, body };
                        Some(ItemWrap{ attrs, is_pub, detail })
                    },
                    Some(_) => unreachable!(), // eat_fn_tail() never return
                                               // others
                }
            },
        }
    }

    /// If the next TT starts with `>`, eat `>` and return true. Otherwise,
    /// return false.
    fn try_eat_templ_end(&mut self) -> bool {
        match_eat!{ self.tts;
            sym!(">") => true,
            sym!(">>" , loc) => { symBack!(self.tts, ">" , loc); true },
            sym!(">=" , loc) => { symBack!(self.tts, "=" , loc); true },
            sym!(">>=", loc) => { symBack!(self.tts, ">=", loc); true },
            tt => { // something else
                // TODO: fix the syntax of `match_eat!()`
                self.tts.putback(tt);
                false
            },
            _ => true, // <EOF> should stop it
        }
    }

    /// Eat and return a template (including `<>`), or return an empty
    /// template.
    fn eat_templ(&mut self) -> Template<'t> {
        match_eat!{ self.tts;
            sym!("<") => {
                let (v, _) = self.eat_many_sep_tail(
                    symbol_type!(","),
                    Parser::eat_templ_arg,
                    |p| p.try_eat_templ_end(),
                );
                v
            },
            _ => vec![],
        }
    }

    /// Eat a template argument.
    fn eat_templ_arg(&mut self) -> TemplArg<'t> {
        match_eat!{ self.tts;
            lt!(name) => {
                let bound = match_eat!{ self.tts;
                    sym!(":") => Some(self.eat_lifetime_bound()),
                    _ => None,
                };
                TemplArg::Lifetime{ name, bound }
            },
            _ => {
                let name = self.eat_ident();
                let bound = match_eat!{ self.tts;
                    sym!(":") => Some(self.eat_ty(true)),
                    _ => None,
                };
                TemplArg::Ty{ name, bound }
            },
        }
    }

    /// Eat and return `'lt1 + 'lt2 + ...`.
    fn eat_lifetime_bound(&mut self) -> Vec<Lifetime<'t>> {
        let (v, _) = self.eat_many_sep_tail(
            symbol_type!("+"),
            |p| match_eat!{ p.tts;
                lt!(x) => x,
                _ => unreachable!(), // if the next TT is not a lifetime, `end`
            },                       // will return true to stop eating.
            |p| match p.tts.peek(0) {
                Some(&lt!(_)) |
                Some(&sym!("+")) => false,
                _ => true,
            },
        );
        v
    }

    /// Eat and return `where` clause, or return None.
    fn eat_opt_whs(&mut self) -> OptWhere<'t> {
        match_eat!{ self.tts;
            kw!("where") => {
                let (restricts, _) = self.eat_many_sep_tail(
                    symbol_type!(","),
                    Parser::eat_restrict,
                    |p| match p.tts.peek(0) {
                        Some(&tree!(_, delim: Brace, ..)) |
                        Some(&sym!("->")) |
                        Some(&sym!(";")) => true,
                        _ => false,
                    },
                );
                Some(restricts)
            },
            _ => None,
        }
    }

    /// Eat a restriction of where clause.
    fn eat_restrict(&mut self) -> Restrict<'t> {
        match_eat!{ self.tts;
            lt!(lt) => {
                let bound = match_eat!{ self.tts;
                    sym!(":") => self.eat_lifetime_bound(),
                    _ => {
                        self.err_prev("Expect lifetime bounds");
                        vec![]
                    },
                };
                Restrict::LifeBound{ lt, bound }
            },
            _ => {
                let ty = self.eat_ty(true);
                let bound = match_eat!{ self.tts;
                    sym!(":") => self.eat_ty(true),
                    _ => {
                        self.err_prev("Expect trait bounds");
                        Ty::Error
                    },
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
        match_eat!{ self.tts;
            ident!("_") => Pat::Hole,
            lit!(lit) => match_eat!{ self.tts;
                sym!("..."), lit!(lit2) => Pat::Range(lit, lit2),
                _ => Pat::Literal(lit),
            },
            sym!("&") =>
                Pat::Ref(Box::new(self.eat_pat())),
            tree!(loc, delim: Paren, tts) => {
                let (mut v, tail) = self.new_inner(loc, tts)
                                        .eat_many_comma_tail_end(
                    Parser::eat_pat,
                );
                if v.len() == 1 && !tail {
                    Pat::Paren(Box::new(v.pop().unwrap()))
                } else {
                    Pat::Tuple(v)
                }
            },
            _ => {
                let is_ref = eatKw!(self.tts; "ref");
                let is_mut = eatKw!(self.tts; "mut");
                if is_ref || is_mut {
                    let name = self.eat_ident();
                    let pat = match_eat!{ self.tts;
                        sym!("@") => Some(Box::new(self.eat_pat())),
                        _ => None,
                    };
                    Pat::BindLike{ name, is_ref, is_mut, pat }
                } else {
                    self.eat_pat_pathy()
                }
            },
        }
    }

    /// Eat a pattern starting with an identifier,
    fn eat_pat_pathy(&mut self) -> Pat<'t> {
        let name = self.eat_path();
        match_eat!{ self.tts;
            tree!(loc, delim: Paren, tts) => {
                let (v, _) = self.new_inner(loc, tts)
                                 .eat_many_comma_tail_end(
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
                let (v, _) = self.new_inner(loc, tts)
                                 .eat_many_comma_tail_end(
                    Parser::eat_destruct_field,
                );
                Pat::DestructNormal{ name, fields: v, ellipsis }
            },
            _ => if let (false, 1, Some(&PathComp::Name{ name, hint: None })) =
                    (name.is_absolute, name.comps.len(), name.comps.first()) {
                let pat = match_eat!{ self.tts;
                    sym!("@") => Some(Box::new(self.eat_pat())),
                    _ => None,
                };
                Pat::BindLike{ name, is_ref: false, is_mut: false, pat }
            } else {
                Pat::Path(name)
            },
        }
    }

    /// Eat and return a field of pattern on struct with fields.
    fn eat_destruct_field(&mut self) -> DestructField<'t> {
        let is_ref = eatKw!(self.tts; "ref");
        let is_mut = eatKw!(self.tts; "mut");
        let name = self.eat_ident();
        let pat = match_eat!{ self.tts;
            sym!(":") => Some(Box::new(self.eat_pat())),
            _ => None,
        };
        DestructField{ is_ref, is_mut, name, pat }
    }

    /// Eat and return a type. If `accect_traits`, it can accept
    /// `Tr1 + Tr2 + ..`.
    fn eat_ty(&mut self, accept_traits: bool) -> Ty<'t> {
        match_eat!{ self.tts;
            ident!("_") => Ty::Hole,
            sym!("!") => Ty::Never,
            tree!(loc, delim: Paren, tts) => {
                let (mut v, tail) = self.new_inner(loc, tts)
                                        .eat_many_comma_tail_end(
                    |p| p.eat_ty(true),
                );
                if v.len() == 1 && !tail {
                    Ty::Paren(Box::new(v.pop().unwrap()))
                } else {
                    Ty::Tuple(v)
                }
            },
            tree!(loc, delim: Bracket, tts) => {
                let mut p = self.new_inner(loc, tts);
                let ty = Box::new(p.eat_ty(true));
                match_eat!{ p.tts;
                    sym!(";") => {
                        let size = Box::new(p.eat_expr(false, true));
                        p.expect_end();
                        Ty::Array{ ty, size }
                    },
                    _ => {
                        p.expect_end();
                        Ty::Slice(ty)
                    },
                }
            },
            sym!("&") => {
                let lt = match_eat!{ self.tts;
                    lt!(lt) => Some(lt),
                    _ => None,
                };
                let is_mut = eatKw!(self.tts; "mut");
                let ty = Box::new(self.eat_ty(false));
                Ty::Ref{ lt, is_mut, ty }
            },
            sym!("*"), kw!("const") =>
                Ty::Ptr{ is_mut: false, ty: Box::new(self.eat_ty(false)) },
            sym!("*"), kw!("mut") =>
                Ty::Ptr{ is_mut: true, ty: Box::new(self.eat_ty(false)) },
            kw!("fn") =>
                self.eat_func_ty(false, ABI::Normal),
            kw!("extern"), kw!("fn") =>
                self.eat_func_ty(false, ABI::Extern),
            kw!("extern"), lit_str!(abi, loc), kw!("fn") =>
                self.eat_func_ty(false, ABI::Specific{ loc, abi }),
            kw!("unsafe"), kw!("fn") =>
                self.eat_func_ty(true, ABI::Normal),
            kw!("unsafe"), kw!("extern"), kw!("fn") =>
                self.eat_func_ty(true, ABI::Extern),
            kw!("unsafe"), kw!("extern"), lit_str!(abi, loc), kw!("fn") =>
                self.eat_func_ty(true, ABI::Specific{ loc, abi }),
            _ => if accept_traits {
                let (mut v, tail) = self.eat_many_sep_tail(
                    symbol_type!("+"),
                    Parser::eat_ty_apply,
                    |p| match p.tts.peek(0) {
                        Some(&sym!("+")) => false,
                        _ => !p.is_ty_apply_begin()
                    },
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
        match self.tts.peek(0) {
            Some(&sym!("::")) |
            Some(&ident!(_)) |
            Some(&kw!("Self")) => true,
            _ => false,
        }
    }

    /// Eat and return a simple type or angle applicated type. It always
    /// returns a `TyApply::Apply`.
    fn eat_opt_angle_ty_apply_args(&mut self) -> Option<Vec<TyApplyArg<'t>>> {
        match_eat!{ self.tts;
            sym!("<") => {
                let (args, _) = self.eat_many_sep_tail(
                    symbol_type!(","),
                    Parser::eat_ty_apply_arg,
                    |p| p.try_eat_templ_end(),
                );
                Some(args)
            },
            _ => None,
        }
    }


    fn eat_ty_apply(&mut self) -> TyApply<'t> {
        let name = self.eat_path();
        match_eat!{ self.tts;
            tree!(loc, delim: Paren, tts) => {
                let (args, _) = self.new_inner(loc, tts)
                                    .eat_many_comma_tail_end(
                    |p| p.eat_ty(true),
                );
                let ret_ty = self.eat_opt_ret_ty();
                TyApply::Paren{ name, args, ret_ty }
            },
            _ => {
                let args = self.eat_opt_angle_ty_apply_args()
                               .unwrap_or_else(|| vec![]);
                TyApply::Angle{ name, args }
            },
        }
    }

    /// Eat and return an argument of parameterized generic type, one of the
    /// arguments inside angles of `T<'a, i32, K=i32>`.
    fn eat_ty_apply_arg(&mut self) -> TyApplyArg<'t> {
        match_eat!{ self.tts;
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
    fn eat_func_ty(&mut self, is_unsafe: bool, abi: ABI<'t>) -> Ty<'t> {
        let (args, va_) = match_eat!{ self.tts;
            tree!(loc, delim: Paren, tts) => {
                self.new_inner(loc, tts).eat_many_comma_tail_last(
                    |p| match_eat!{ p.tts;
                        ident!(name), sym!(":") =>
                            FuncTyParam{ name: Some(Ok(name))
                                       , ty: p.eat_ty(true) },
                        _ => FuncTyParam{ name: None
                                        , ty: p.eat_ty(true) },
                    },
                    |p| match_eat!{ p.tts;
                        sym!("...") => Some(()),
                        _ => None,
                    },
                    |p| p.is_end(),
                )
            },
            _ => {
                self.err_prev("Expect the parameter list");
                (vec![], None)
            },
        };
        let ret_ty = self.eat_opt_ret_ty();
        let fun_ty = FuncTy{
            is_unsafe,
            abi,
            args,
            is_va: va_.is_some(),
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
                    match_eat!{ self.tts;
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
                match_eat!{ self.tts;
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
        let op = match_eat!{ self.tts;
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
            match_eat!{ self.tts;
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
                    match_eat!{ self.tts;
                        tree!(loc, delim: Paren, tts) => {
                            let (args, _) = self.new_inner(loc, tts)
                                                .eat_many_comma_tail_end(
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
                    let mut p = self.new_inner(loc, tts);
                    let brk_loc = &loc[..1]; // `[`
                    let index = Box::new(p.eat_expr(false, true));
                    p.expect_end();
                    e = Expr::Index {
                        obj: Box::new(e),
                        brk_loc,
                        index,
                    };
                },
                tree!(loc, delim: Paren, tts) => {
                    let par_loc = &loc[..1]; // `(`
                    let (args, _) = self.new_inner(loc, tts)
                                        .eat_many_comma_tail_end(
                        |p| p.eat_expr(false, true),
                    );
                    e = Expr::Call{ func: Box::new(e), par_loc, args };
                },
                _ => return e,
            }
        }
    }

    /// Eat and return a block expression. If the next TT is tree delimitted by
    /// braces, it will return `Expr::Error`.
    fn eat_block_expr(&mut self) -> Expr<'t> {
        match_eat!{ self.tts;
            tree!(loc, delim: Brace, tts) =>
                self.new_inner(loc, tts).eat_block_expr_inner_end(),
            _ => Expr::Error,
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
        match_eat!{ self.tts;
            lit!(lit) => Expr::Literal(lit),
            tree!(loc, delim: Paren, tts) => {
                let (mut v, tail) = self.new_inner(loc, tts)
                                        .eat_many_comma_tail_end(
                    |p| p.eat_expr(false, true),
                );
                if v.len() == 1 && !tail {
                    Expr::Paren(Box::new(v.pop().unwrap()))
                } else {
                    Expr::Tuple(v)
                }
            },
            tree!(loc, delim: Bracket, tts) =>
                self.new_inner(loc, tts).eat_array_expr_inner_end(),
            tree!(loc, delim: Brace, tts) =>
                self.new_inner(loc, tts).eat_block_expr_inner_end(),
            kw!("unsafe") =>
                Expr::Unsafe(Box::new(self.eat_block_expr())),
            sym!("|", loc) =>
                self.eat_lambda_expr_tail(false, loc, false),
            sym!("||", loc) =>
                self.eat_lambda_expr_tail(false, &loc[..1], true),
            kw!("move"), sym!("|", loc) =>
                self.eat_lambda_expr_tail(true, loc, false),
            kw!("move"), sym!("||", loc) =>
                self.eat_lambda_expr_tail(true, &loc[..1], true),
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
                    match_eat!{ self.tts;
                        tree!(loc, delim: Brace, tts) => {
                            let (fields, base) =
                                self.new_inner(loc, tts)
                                    .eat_expr_struct_inner_end();
                            Some((fields, base))
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
        let body = Box::new(self.eat_block_expr());
        Expr::Loop{ label, body }
    }

    /// Eat and return the while expression after `while`.
    fn eat_while_tail(&mut self, label: Option<Lifetime<'t>>) -> Expr<'t> {
        match_eat!{ self.tts;
            kw!("let") => {
                let pat = Box::new(self.eat_pat());
                let expr = match_eat!{ self.tts;
                    sym!("=") => self.eat_expr(false, false),
                    _ => Expr::Error,
                };
                let body = Box::new(self.eat_block_expr());
                Expr::WhileLet {
                    pat,
                    expr: Box::new(expr),
                    body,
                }
            },
            _ => {
                let cond = Box::new(self.eat_expr(false, false));
                let body = Box::new(self.eat_block_expr());
                Expr::While{ label, cond, body }
            },
        }
    }

    /// Eat and return the for expression after `for`.
    fn eat_for_tail(&mut self, label: Option<Lifetime<'t>>) -> Expr<'t> {
        let pat = Box::new(self.eat_pat());
        let iter = match_eat!{ self.tts;
            kw!("in") => Box::new(self.eat_expr(false, false)),
            _ => Box::new(Expr::Error),
        };
        let body = Box::new(self.eat_block_expr());
        Expr::For{ label, pat, iter, body}
    }

    /// Eat and return the if expression after `if`.
    fn eat_if_tail(&mut self) -> Expr<'t> {
        let then_else = |p: &mut Self| {
            let then_expr = Box::new(p.eat_block_expr());
            let else_expr = match_eat!{ p.tts;
                kw!("else"), kw!("if") => Some(Box::new(p.eat_if_tail())),
                kw!("else") => Some(Box::new(p.eat_block_expr())),
                _ => None,
            };
            (then_expr, else_expr)
        };
        match_eat!{ self.tts;
            kw!("let") => {
                let pat = Box::new(self.eat_pat());
                let match_expr = match_eat!{ self.tts;
                    sym!("=") => Box::new(self.eat_expr(false, false)),
                    _ => Box::new(Expr::Error),
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
        let arms = match_eat!{ self.tts;
            tree!(loc, delim: Brace, tts) => {
                let (arms, _) = self.new_inner(loc, tts)
                                    .eat_many_comma_tail_end(
                    |p| {
                        let pats = p.eat_many_sep(
                            symbol_type!("|"),
                            "Expect a pattern",
                            Parser::eat_pat,
                            |p| match p.tts.peek(0) {
                                Some(&sym!("|")) => false,
                                _ => !p.is_pat_begin(),
                            },
                        );
                        let cond = match_eat!{ p.tts;
                            kw!("if") =>
                                Some(Box::new(p.eat_expr(false, true))),
                            _ => None,
                        };
                        let expr = match_eat!{ p.tts;
                            sym!("=>") => p.eat_expr(false, true),
                            _ => Expr::Error,
                        };
                        MatchArm{ pats, cond, expr: Box::new(expr) }
                    },
                );
                arms
            },
            _ => {
                self.err_prev("Expect the body in `{}`");
                vec![]
            },
        };
        Expr::Match{ kw_loc, expr, arms }
    }

    /// Eat the inner of a block expression to the end, and return the block
    /// expression.
    fn eat_block_expr_inner_end(mut self) -> Expr<'t> {
        let eat_semi = |p: &mut Self| match_eat!{ p.tts;
            sym!(";") => true,
            _ => false,
        };
        let attrs = self.eat_inner_attrs();
        let mut stmts = vec![];
        let mut ret: Option<Expr> = None;
        while !self.is_end() {
            if let Some(expr) = ret.take() { // .. <expr> |;
                if !expr.is_item_like() {
                    self.expect_semi();
                }
                let stmt = match expr {
                    Expr::PluginInvoke(p) =>
                        Stmt::PluginInvoke(p),
                    _ => Stmt::Expr(expr),
                };
                stmts.push(stmt);
            } else if eat_semi(&mut self) { // .. <expr>; |;
                // NOP
            } else if self.is_item_begin() {
                if let Some(item) = self.eat_item() {
                    stmts.push(Stmt::Item(Box::new(item)));
                }
            } else { match_eat!{ self.tts;
                kw!("let") => {
                    let pat = self.eat_pat();
                    let ty = match_eat!{ self.tts;
                        sym!(":") => self.eat_ty(true),
                        _ => Ty::Error,
                    };
                    let expr = match_eat!{ self.tts;
                        sym!("=") => self.eat_expr(false, true),
                        _ => Expr::Error,
                    };
                    self.expect_semi();
                    stmts.push(Stmt::Let {
                        pat,
                        ty: Box::new(ty),
                        expr: Box::new(expr),
                    });
                },
                _ => if self.is_expr_begin() {
                    ret = Some(self.eat_expr(true, true));
                } else {
                    let (_, loc) = self.tts.next().unwrap(); // not `is_end()`
                    self.err(loc, "Unknow beginning of statement");
                },
            }}
        }
        Expr::Block{ attrs, stmts, ret: ret.map(Box::new) }
    }

    /// Eat the inner of a array literal or filled array to the end, and return
    /// the Expr::ArrayFill or Expr::ArrayLit.
    fn eat_array_expr_inner_end(mut self) -> Expr<'t> {
        let e0 = self.eat_expr(false, true);
        match_eat!{ self.tts;
            sym!(";") => {
                let elem = Box::new(e0);
                let len = Box::new(self.eat_expr(false, true));
                self.expect_end();
                Expr::ArrayFill{ elem, len }
            },
            _ => {
                match_eat!{ self.tts;
                    sym!(",") => (),
                    _ => (),
                };
                let (mut elems, _) = self.eat_many_comma_tail_end(
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
        match_eat!{ self.tts;
            sym!("|") => true,
            sym!("||", loc) => { symBack!(self.tts, "|", loc); true },
            sym!("|=", loc) => { symBack!(self.tts, "=", loc); true },
            _ => false,
        }
    }

    /// Eat and return a lambda expression after `[move] |` or `[move] ||`.
    fn eat_lambda_expr_tail(
        &mut self,
        is_move:   bool,
        loc:       LocStr<'t>,
        is_closed: bool,
    ) -> Expr<'t> {
        let args = if is_closed {
            vec![]
        } else {
            let (v, _) = self.eat_many_sep_tail(
                symbol_type!(","),
                Parser::eat_lambda_param,
                Parser::try_eat_lambda_arg_end,
            );
            v
        };
        let (ret_ty, body) = match_eat!{ self.tts;
            sym!("->") => (
                Some(Box::new(self.eat_ty(true))),
                Box::new(self.eat_block_expr()),
            ),
            _ => (
                None,
                Box::new(self.eat_expr(false, true)),
            ),
        };
        let sig = Box::new(LambdaSig{ is_move, loc, args, ret_ty });
        Expr::Lambda{ sig, body }
    }

    /// Eat and return a parameter of lambda function.
    fn eat_lambda_param(&mut self) -> FuncParam<'t> {
        let pat = self.eat_pat();
        let ty = match_eat!{ self.tts;
            sym!(":") => self.eat_ty(true),
            _ => Ty::Error,
        };
        FuncParam::Bind{ pat, ty: Box::new(ty) }
    }

    /// Eat the content inside the brace of struct expression `S{ .. }` to the
    /// end.
    fn eat_expr_struct_inner_end(
        &mut self,
    ) -> (Vec<ExprStructField<'t>>, Option<Box<Expr<'t>>>) {
        let (v, base) = self.eat_many_comma_tail_last(
            |p| {
                let name = p.eat_ident();
                let expr = match_eat!{ p.tts;
                    sym!(":") => Some(Box::new(p.eat_expr(false, true))),
                    _ => None,
                };
                ExprStructField{ name, expr }
            },
            |p| match_eat!{ p.tts;
                sym!("..") => Some(Box::new(p.eat_expr(false, true))),
                _ => None,
            },
            |p| p.is_end(),
        );
        (v, base)
    }

    /// Eat and return an plugin invoke, or return None.
    fn eat_opt_plugin_invoke(&mut self) -> Option<PluginInvoke<'t>> {
        match_eat!{ self.tts;
            ident!(name), sym!("!") => {
                let ident = match_eat!{ self.tts;
                    ident!(s) => Some(Ok(s)),
                    _ => None,
                };
                match_eat!{ self.tts;
                    tt@tree!(_, ..) =>
                        Some(PluginInvoke{ name: Ok(name), ident, tt }),
                    _ => {
                        self.err_prev("Expect token tree (`()`, `[]`, `{}`)");
                        None
                    },
                }
            },
            _ => None,
        }
    }
}
