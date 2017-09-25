extern crate mair;
use std::fs::*;
use std::path::{Path, PathBuf};
use std::io::{self, Read, Write};
use std::ffi::OsStr;
use mair::parse::str_ptr_diff;
use mair::parse::error::*;
use mair::parse::lexer::*;
use mair::parse::parser::*;
use mair::parse::ast::*;

fn test_dir_helper<P: AsRef<Path>, F: Fn(&mut Write, &str) -> io::Result<()>>(
    path: P,
    f: F,
) -> io::Result<bool> {
    let mut passed = true;
    for dirent in read_dir(path)? {
        let pathi = dirent?.path();
        if pathi.extension() == Some(&OsStr::new("in")) {
            println!("testing {}", pathi.display());
            let patho = pathi.with_extension("out");
            let mut si = String::new();
            let mut vo = vec![];
            File::open(&pathi)?
                .read_to_string(&mut si)?;
            File::open(&patho)?
                .read_to_end(&mut vo)?;
            let mut buf = vec![];
            f(&mut buf, &si)?;
            if vo == buf {
                println!("ok");
            } else {
                File::create(&patho)?
                    .write_all(&buf)?;
                passed = false;
                println!("fail");
            }
        }
    }
    Ok(passed)
}

fn test_dir<F: Fn(&mut Write, &str) -> io::Result<()>>(dir: &str, f: F) {
    let mut path = PathBuf::new();
    path.push(".");
    path.push("tests");
    path.push(dir);
    match test_dir_helper(path, f) {
        Err(e) => panic!("os error: {:?}", e),
        Ok(false) => panic!("test fail"),
        Ok(true) => (),
    }
}

fn test_dir_lines<F: Fn(&mut Write, &str) -> io::Result<()>>(dir: &str, f: F) {
    test_dir(dir, |mut fo, s| {
        for (i, line) in s.lines().enumerate() {
            print!("#{} ", i + 1);
            f(&mut fo, line)?
        }
        println!("");
        Ok(())
    });
}

fn lex(input: &str) -> Result<Vec<Token>, LexicalError> {
    let mut v = vec![];
    for c in Lexer::new(input) {
        v.push(c?);
    }
    Ok(v)
}

fn tts(input: &str) -> Result<Vec<TT>, UnmatchedDelimError> {
    let ltoks = lex(input).unwrap();
    parse_tts(input, &ltoks)
}

fn parse(input: &str) -> (Mod, Vec<HardSyntaxError>) {
    let tts_ = tts(input).unwrap();
    parse_crate(input, tts_)
}

#[test]
fn parse_test() {
    test_dir_lines("lexer_unit", |f, s| {
        writeln!(f, "{:?}", lex(s))
    });
    test_dir("lexer_large", |f, s| {
        writeln!(f, "{:?}", lex(s))
    });
    test_dir_lines("tts_simple", |f, s| {
        writeln!(f, "{:?}", tts(s))
    });
    test_dir("tts_large", |f, s| {
        writeln!(f, "{:?}", tts(s))
    });
    test_dir("parser_large", |f, s| {
        let (m, v) = parse(s);
        writeln!(f, "{:?}", m)?;
        for HardSyntaxError{ loc, reason } in v {
            writeln!(f, "{}..{} {:?} {}",
                str_ptr_diff(loc, s),
                str_ptr_diff(&loc[loc.len()..], s),
                loc,
                reason,
            )?;
        }
        Ok(())
    });
}
