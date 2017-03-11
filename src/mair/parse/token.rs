use std::str::from_utf8_unchecked;
use std::char::from_u32;
use super::ptr_diff;
use self::DelimToken::*;
use self::TokenizeError::*;
use self::Token::*;
use self::LiteralType::*;

type RawErr<'a> = TokenizeError<&'a [u8]>;

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum TokenizeError<Pos=usize> {
    UnclosedComment(Pos),
    UnmatchedDelimiter(Pos, Pos),
    UnterminatedStr(Pos),
    InvalidRawStrBegin(Pos),
    InvalidEscape(Pos),
    InvalidNumLit(Pos),
    UnexpectedChar(Pos),
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum DelimToken {
    Paren,
    Bracket,
    Brace,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Token<'a> {
    Delimited(DelimToken, Vec<Token<'a>>),
    InnerDoc(&'a str),
    OuterDoc(&'a str),
    Ident(&'a str),
    Lifetime(&'a str),  // excluding leader `'`
    Symbol(&'a str),
    Literal(LiteralType),
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum LiteralType {
    Char, Str, ByteStr,
    Int, Float,
    I8, I16, I32, I64, ISize,
    U8, U16, U32, U64, USize,
    F32, F64,
}

/// Parse source string into a list of tokens.
pub fn tokenize(source: &str) -> Result<Vec<Token>, TokenizeError> {
    let index_of = |ns: &[u8]| ptr_diff(ns.as_ptr(), source.as_ptr()) as usize;
    match tokens(source.as_bytes()) {
        Ok((tail, tts)) => if tail.is_empty() {
            Ok(tts)
        } else {
            Err(UnexpectedChar(index_of(tail)))
        },
        Err(e)          => match e {
            UnclosedComment(beg)         =>
                Err(UnclosedComment(index_of(beg))),
            UnmatchedDelimiter(beg, end) =>
                Err(UnmatchedDelimiter(index_of(beg), index_of(end))),
            UnterminatedStr(pos)         =>
                Err(UnterminatedStr(index_of(pos))),
            InvalidRawStrBegin(pos)      =>
                Err(InvalidRawStrBegin(index_of(pos))),
            InvalidEscape(pos)           =>
                Err(InvalidEscape(index_of(pos))),
            InvalidNumLit(pos)           =>
                Err(InvalidNumLit(index_of(pos))),
            UnexpectedChar(pos)          =>
                Err(UnexpectedChar(index_of(pos))),
        },
    }
}

macro_rules! match_head {
    ($s:expr; _ => $e:expr;) => ($e);
    ($s:expr; pat ($($pat:pat)|+) => $e:expr; $($tt:tt)*) => ({
        match $s[0] {
            $($pat)|+ => $e,
            _         => match_head!($s; $($tt)*),
        }
    });
    ($s:expr; $($pat:expr),+ => $e:expr; $($tt:tt)*) => ({
        if [$(&$pat[..]),+].iter().any(|p| $s.starts_with(p)) {
            $e
        } else {
            match_head!($s; $($tt)*)
        }
    });
    ($s:expr; $($pat:expr),+; $(($c:ident))* => $e:expr; $($tt:tt)*) => ({
        if let Some(c) = [$(&$pat[..]),+].iter().find(|p| $s.starts_with(p)) {
            $(let $c = &$s[..c.len()];)*
            $s = &$s[c.len()..];
            $e
        } else {
            match_head!($s; $($tt)*)
        }
    });
}

/// Helper parser for `tokenize`.
fn tokens(mut s: &[u8]) -> Result<(&[u8], Vec<Token>), RawErr> {
    let mut v = vec![];
    macro_rules! delimited { ($r:expr, $dm:expr) => {{
            let (mut ns, tts) = tokens(&s[1..])?;
            if trim(&mut ns) && ns[0] == $r {
                v.push(Delimited($dm, tts));
                s = &ns[1..];
            } else {
                return Err(UnmatchedDelimiter(s, ns));
            }
        }}; }
    while trim(&mut s) {
        match_head!(s;
            b")", b"]", b"}" => break;
            b"("        => delimited!(b')', Paren);
            b"["        => delimited!(b']', Bracket);
            b"{"        => delimited!(b'}', Brace);
            b"//!" ;    => v.push(InnerDoc(line_comment_inner(&mut s)));
            b"////";    => { line_comment_inner(&mut s); };
            b"///" ;    => v.push(OuterDoc(line_comment_inner(&mut s)));
            b"//"  ;    => { line_comment_inner(&mut s); };
            b"/*!" ;    => v.push(InnerDoc(block_comment_inner(&mut s)?));
            b"/***";    => { block_comment_inner(&mut s)?; };
            b"/**" ;    => v.push(OuterDoc(block_comment_inner(&mut s)?));
            b"/*"  ;    => { block_comment_inner(&mut s)?; };
            b"0x"  ;    => v.push(int_lit(&mut s, 16, true)?);
            b"0o"  ;    => v.push(int_lit(&mut s, 8,  true)?);
            b"0b"  ;    => v.push(int_lit(&mut s, 2,  true)?);
            pat (b'0'...b'9') => v.push(num_lit(&mut s)?);
            b"\"", b"r\"", b"r#", b"b\"", b"br\"", b"br#" =>
                v.push(string_lit(&mut s)?);
            b"::", b"->", b"=>",
            b"==", b"!=", b"<=", b">=",
            b"&&", b"||",
            b"!", b"=",
            b"+=", b"-=", b"*=", b"/=", b"%=",
            b"&=", b"|=", b"^=", b"<<=", b">>=",
            b"+", b"-", b"*", b"/", b"%",
            b"&", b"|", b"^", b"<<", b">>",
            b"<", b">"; (c) =>
                v.push(Symbol(to_str(c)));
            pat (b'_' | b'a'...b'z' | b'A'...b'Z') => { // identifier
                let mut i = 1;
                while i < s.len() { match s[i] {
                    b'_' | b'a'...b'z' | b'A'...b'Z' | b'0'...b'9' => i += 1,
                    _ => break,
                }}
                v.push(Ident(to_str(&s[..i])));
                s = &s[i..];
            };
            _ => unimplemented!();
        );
    }
    Ok((s, v))
}

/// Parse integer or float literal.
fn num_lit<'a>(s: &mut &'a [u8]) -> Result<Token<'a>, RawErr<'a>> {
    let mut ns = *s;
    let e = InvalidNumLit(ns);
    macro_rules! consume_int { () => (
        int_lit(&mut ns, 10, false).map_err(|_| e)?
    ) };
    int_lit(&mut ns, 10, false)?;
    let mut ty = match_head!(ns;
        b"._"            => return Err(e); // `1._2` in invalid
        b"." ;           => { consume_int!(); Float };
        _                => Int;
    );
    ty = match_head!(ns;
        b"e", b"E" => {
            ns = &ns[1..];
            match_head!(ns;
                b"-", b"+" => ns = &ns[1..]; // `1e-1`
                _          => {};
            );
            consume_int!();
            Float
        };
        _          => ty;
    );
    match_head!(ns;
        b"i", b"u", b"f" => if let Some(nty) = num_suffix(&mut ns, true) {
            if ty == Float && (nty != F32 && nty != F64) { // `1.2i32` is invalid
                return Err(e);
            }
            ty = nty;
        } else { return Err(e) };
        _                => {};
    );
    *s = ns;
    Ok(Literal(ty))
}

/// Parse integer literal.
fn int_lit<'a>(s: &mut &'a [u8], radix: u32, suffix: bool) ->
        Result<Token<'a>, RawErr<'a>> {
    assert!([2, 8, 10, 16].contains(&radix));
    let mut ns = *s;
    let mut ty = None;
    while !ns.is_empty() { match ns[0] {
        b'_' => ns = &ns[1..],
        b'i' | b'u' if suffix => {
            ty = ty.and_then(|_| num_suffix(&mut ns, false));
            break;
        },
        c@b'0'...b'9'  =>
            if (c as char).to_digit(radix).is_some() {
                ty = Some(Int);
                ns = &ns[1..];
            } else { ty = None; break; },
        b'a'...b'f' | b'A'...b'F' if radix == 16 => {
            ty = Some(Int);
            ns = &ns[1..];
        },
        _ => break,
    }}
    match ty {
        Some(t) => { *s = ns; Ok(Literal(t)) },
        None    => Err(InvalidNumLit(*s)),
    }
}

/// Parse a number suffix.
fn num_suffix<'a>(s: &mut &'a [u8], float: bool) -> Option<LiteralType> {
    match_head!(*s;
        b"i8"   ;   => Some(I8);
        b"i16"  ;   => Some(I16);
        b"i32"  ;   => Some(I32);
        b"i64"  ;   => Some(I64);
        b"isize";   => Some(ISize);
        b"u8"   ;   => Some(U8);
        b"u16"  ;   => Some(U16);
        b"u32"  ;   => Some(U32);
        b"u64"  ;   => Some(U64);
        b"usize";   => Some(USize);
        _           => if float {
            match_head!(*s;
                b"f32"; => Some(F32);
                b"f64"; => Some(F64);
                _       => None;
            )
        } else { None };
    )
}

/// Parse an string literal ("" r"" b"" br"").
fn string_lit<'a>(s: &mut &'a [u8]) -> Result<Token<'a>, RawErr<'a>> {
    let ok = if s[0] == b'b' {
        *s = &s[1..];
        Ok(Literal(ByteStr))
    } else { Ok(Literal(Str)) };
    let raw = s[0] == b'r'; if raw { *s = &s[1..]; }
    let mut hashes = 0;
    while s.first() == Some(&b'#') { hashes += 1; *s = &s[1..]; }
    if s.first() == Some(&b'"') {
        let begin = *s;
        *s = &s[1..];
        let mut cnt = -1;
        while !s.is_empty() {
            match s[0] {
                b'"'             => cnt = 0,
                b'\\' if !raw    => {
                    eat_escaped(s)?;
                    cnt = -1;
                    continue;
                },
                b'#' if cnt >= 0 => {
                    cnt += 1;
                },
                _                => cnt = -1,
            }
            *s = &s[1..];
            if cnt == hashes { return ok; }
        }
        Err(UnterminatedStr(begin))
    } else { Err(InvalidRawStrBegin(*s)) }
}

/// Consume an escaped char (including leading `\`).
fn eat_escaped<'a>(s: &mut &'a [u8]) -> Result<(), RawErr<'a>> {
    assert!(s[0] == b'\\');
    if s.len() == 1 { return Err(InvalidEscape(*s)); }
    match s[1] {
        b'\\' | b'n' | b'r' | b't' | b'0' |
        b'"' | b'\'' | b'\n' | b'\r' => { *s = &s[2..] },
        b'x' => if s.len() < 4 ||
                   !(s[2] as char).is_digit(8) ||
                   !(s[3] as char).is_digit(16) {
            return Err(InvalidEscape(*s));
        } else { *s = &s[4..]; },
        b'u' if s.len() >= 5 && s[2] == b'{' => {
            let mut i = 0;
            let mut code = 0u32;
            while i < 6 && 3 + i < s.len() {
                if let Some(x) = (s[3 + i] as char).to_digit(16) {
                    code = code << 4 | x;
                } else { break }
                i += 1;
            }
            i += 3; // `\u{`
            if s.get(i) != Some(&b'}') || from_u32(code).is_none() {
                return Err(InvalidEscape(s));
            }
            *s = &s[i+1..];
        },
        _    => return Err(InvalidEscape(*s)),
    }
    Ok(())
}

/// Parse the body of line comment(excluding '//') and return it.
fn line_comment_inner<'a>(s: &mut &'a [u8]) -> &'a str {
    let mut i = 0;
    while i < s.len() && !b"\r\n".contains(&s[i]) { i += 1 }
    let ret = to_str(&s[..i]);
    *s = &s[i..];
    ret
}

/// Parse the body of block comment(excluding '/*') recursively and return it.
fn block_comment_inner<'a>(s: &mut &'a [u8]) -> Result<&'a str, RawErr<'a>> {
    let mut ns = *s;
    let mut begins = vec![*s];
    while !begins.is_empty() { match ns.first() {
        None                                   =>
            return Err(UnclosedComment(begins.last().unwrap())),
        Some(&b'*') if s.get(1) == Some(&b'/') => {
            begins.pop();
            ns = &ns[2..];
        } ,
        Some(&b'/') if s.get(1) == Some(&b'*') => {
            begins.push(ns);
            ns = &ns[2..];
        },
        _                                      =>
            ns = &ns[1..],
    }}
    let ret = to_str(&s[..(ptr_diff(ns.as_ptr(), s.as_ptr()) as usize - 2)]);
    *s = ns;
    Ok(ret)
}

/// Remove leading spaces and return whether there's something left
fn trim(s: &mut &[u8]) -> bool {
    while !s.is_empty() { match s[0] {
        b' ' | 0x09...0x0D => *s = &s[1..], // b" \t\n\v\f\r"
        _ => break,
    } }
    !s.is_empty()
}

/// A shortcut to `std::str::from_utf8_unchecked`
fn to_str(s: &[u8]) -> &str { unsafe{ from_utf8_unchecked(s) } }

#[test]
fn test_num_lit() {
    let mut s: &[u8];
    for &(c, rdx, suf, ref r, t) in [
        (&b"_"[..],       10, true,  Err(InvalidNumLit(&b"_"[..])),      &b"_"[..]),
        (&b"i32"[..],     10, true,  Err(InvalidNumLit(&b"i32"[..])),    &b"i32"[..]),
        (&b"10_01."[..],  2,  true,  Ok(Literal(Int)),                   &b"."[..]),
        (&b"1u32 "[..],   10, true,  Ok(Literal(U32)),                   &b" "[..]),
        (&b"1u32 "[..],   10, false, Ok(Literal(Int)),                   &b"u32 "[..]),
        (&b"_0_u9 "[..],  10, true,  Err(InvalidNumLit(&b"_0_u9 "[..])), &b"_0_u9 "[..]),
        (&b"_0_u9 "[..],  10, false, Ok(Literal(Int)),                   &b"u9 "[..]),
        (&b"0f64"[..],    10, true,  Ok(Literal(Int)),                   &b"f64"[..]),
        (&b"678."[..],    10, true,  Ok(Literal(Int)),                   &b"."[..]),
        (&b"678."[..],    8,  true,  Err(InvalidNumLit(&b"678."[..])),   &b"678."[..]),
        (&b"1234 89"[..], 10, true,  Ok(Literal(Int)),                   &b" 89"[..]),
    ].iter() {
        println!("{} {} {} {:?} {}", to_str(c), rdx, suf, r, to_str(t));
        s = c;
        assert_eq!(int_lit(&mut s, rdx, suf), *r);
        assert_eq!(s, t);
    }
    for &(c, ref r, t) in [
        (&b"0"[..],         Ok(Literal(Int)),   &b""[..]),
        (&b"0i8"[..],       Ok(Literal(I8)),    &b""[..]),
        (&b"0i16"[..],      Ok(Literal(I16)),   &b""[..]),
        (&b"0i32"[..],      Ok(Literal(I32)),   &b""[..]),
        (&b"0i64"[..],      Ok(Literal(I64)),   &b""[..]),
        (&b"0isize"[..],    Ok(Literal(ISize)), &b""[..]),
        (&b"0u8"[..],       Ok(Literal(U8)),    &b""[..]),
        (&b"0u16"[..],      Ok(Literal(U16)),   &b""[..]),
        (&b"0u32"[..],      Ok(Literal(U32)),   &b""[..]),
        (&b"0u64"[..],      Ok(Literal(U64)),   &b""[..]),
        (&b"0usize"[..],    Ok(Literal(USize)), &b""[..]),
        (&b"0f32"[..],      Ok(Literal(F32)),   &b""[..]),
        (&b"0f64"[..],      Ok(Literal(F64)),   &b""[..]),
        (&b"1.2"[..],       Ok(Literal(Float)), &b""[..]),
        (&b"1e1"[..],       Ok(Literal(Float)), &b""[..]),
        (&b"1e-1"[..],      Ok(Literal(Float)), &b""[..]),
        (&b"1e+1"[..],      Ok(Literal(Float)), &b""[..]),
        (&b"1.1e1"[..],     Ok(Literal(Float)), &b""[..]),
        (&b"1.1e-1"[..],    Ok(Literal(Float)), &b""[..]),
        (&b"1_.1_e-_1"[..], Ok(Literal(Float)), &b""[..]),
        (&b"1.2f32"[..],    Ok(Literal(F32)),   &b""[..]),
        (&b"1+"[..],        Ok(Literal(Int)),   &b"+"[..]),
        (&b"1a32"[..],      Ok(Literal(Int)),   &b"a32"[..]),
        (&b"1.2i32"[..],    Err(InvalidNumLit(&b"1.2i32"[..])), &b"1.2i32"[..]),
        (&b"1e2i32"[..],    Err(InvalidNumLit(&b"1e2i32"[..])), &b"1e2i32"[..]),
        (&b"1i65"[..],      Err(InvalidNumLit(&b"1i65"[..])),   &b"1i65"[..]),
        (&b"1._2"[..],      Err(InvalidNumLit(&b"1._2"[..])),   &b"1._2"[..]),
    ].iter() {
        println!("{} {:?} {}", to_str(c), r, to_str(t));
        s = c;
        assert_eq!(num_lit(&mut s), *r);
        assert_eq!(s, t);
    }
}

#[test]
fn test_string_lit() {
    let mut s: &[u8];
    for &(c, ref r, t) in [
        (&br#""\""."#[..],                 Ok(Literal(Str)),       &b"."[..]),
        (&br#"b"a"."#[..],                 Ok(Literal(ByteStr)),   &b"."[..]),
        (&br#"r"\"."#[..],                 Ok(Literal(Str)),       &b"."[..]),
        (&br#"br"b"."#[..],                Ok(Literal(ByteStr)),   &b"."[..]),
        (&br##"r#"#"#."##[..],             Ok(Literal(Str)),       &b"."[..]),
        (&br##"br#"#"#."##[..],            Ok(Literal(ByteStr)),   &b"."[..]),
        (&br###"r##"##"'##"#""##."###[..], Ok(Literal(Str)),       &b"."[..]),
        (&b"\""[..],              Err(UnterminatedStr(&b"\""[..])),      &b""[..]),
        (&b"\"\\??"[..],          Err(InvalidEscape(&b"\\??"[..])),      &b"\\??"[..]),
        (&b"r##"[..],             Err(InvalidRawStrBegin(&b""[..])),     &b""[..]),
        (&b"r## \""[..],          Err(InvalidRawStrBegin(&b" \""[..])),  &b" \""[..]),
        (&br##"r#"a""##[..],      Err(UnterminatedStr(&b"\"a\""[..])), &b""[..]),
        (&br###"r##""# #"###[..], Err(UnterminatedStr(&b"\"\"# #"[..])), &b""[..]),
    ].iter() {
        println!("{} {:?} {}", to_str(c), r, to_str(t));
        s = c;
        assert_eq!(string_lit(&mut s), *r);
        assert_eq!(s, t);
    }
}

#[test]
fn test_escape() {
    let mut s: &[u8];
    for &c in [
        &b"\\"[..], &b"\\="[..], &b"\\x"[..],
        &b"\\xX9"[..], &b"\\x9G"[..], &b"\\x80"[..],
        &b"\\u"[..], &b"\\u{"[..], &b"\\u}"[..], &b"\\u{}"[..],
        &b"\\u{p}"[..], &b"\\u{0p}"[..], &b"\\u{FFFFFF}"[..], &b"\\u{0000000}"[..],
    ].iter() {
        s = c;
        println!("Should fail: {}", to_str(s));
        assert_eq!(eat_escaped(&mut s), Err(InvalidEscape(c)));
        assert_eq!(s, c);
    }
    for &(c, l) in [
        (&b"\\\\\\"[..], 2), (&b"\\x7FF"[..], 4),
        (&b"\\u{2764} "[..], 8), (&b"\\u{10FfFf}"[..], 10)
    ].iter() {
        s = c;
        println!("Should ok: {}", to_str(s));
        assert_eq!(eat_escaped(&mut s), Ok(()));
        assert_eq!(s, &c[l..]);
    }
}

#[test]
fn test_comment_parsing() {
    let mut s: &[u8] = &b""[..];
    assert_eq!(line_comment_inner(&mut s), ""); assert_eq!(s, b"");
    s = &b"a a\ta"[..];
    assert_eq!(line_comment_inner(&mut s), "a a\ta"); assert_eq!(s, b"");
    s = &b" a\n\r"[..];
    assert_eq!(line_comment_inner(&mut s), " a"); assert_eq!(s, b"\n\r");
    s = &b"b \r\n"[..];
    assert_eq!(line_comment_inner(&mut s), "b "); assert_eq!(s, b"\r\n");
    s = &b"\n"[..];
    assert_eq!(line_comment_inner(&mut s), ""); assert_eq!(s, b"\n");
    s = &b"\r"[..];
    assert_eq!(line_comment_inner(&mut s), ""); assert_eq!(s, b"\r");
}

#[test]
fn test_tokenize() {
    assert_eq!(tokenize(""),                Ok(vec![]));
    assert_eq!(tokenize("  hell0 world "),  Ok(vec![Ident("hell0"), Ident("world")]));
    assert_eq!(tokenize("a"),               Ok(vec![Ident("a")]));
    assert_eq!(tokenize("()///[x\r[a]{ /*!//x{\n \t*/b0\n\t_T} "),
        Ok(vec![
            Delimited(Paren,   vec![]),
            OuterDoc("[x"),
            Delimited(Bracket, vec![Ident("a")]),
            Delimited(Brace,   vec![
                InnerDoc("//x{\n \t"),
                Ident("b0"),
                Ident("_T")
            ]),
        ])
    );
    assert_eq!(tokenize("a-=!\"a\"br#\"\"\"#"), Ok(vec![
        Ident("a"),
        Symbol("-="),
        Symbol("!"),
        Literal(Str),
        Literal(ByteStr),
    ]));
    assert_eq!(tokenize("<<="), Ok(vec![Symbol("<<=")]));
    assert_eq!(tokenize("< <="), Ok(vec![Symbol("<"), Symbol("<=")]));
    assert_eq!(tokenize("<< ="), Ok(vec![Symbol("<<"), Symbol("=")]));
    assert_eq!(tokenize("< < ="), Ok(vec![Symbol("<"), Symbol("<"), Symbol("=")]));
}
