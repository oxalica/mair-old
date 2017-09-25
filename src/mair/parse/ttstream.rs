use std::ptr::copy_nonoverlapping;
use std::mem::{uninitialized, forget};
use super::ast::TT;

#[derive(Clone)]
pub struct TTStream<'a>(Vec<TT<'a>>, &'a str);

impl<'a> TTStream<'a> {
    pub fn new(mut tts: Vec<TT<'a>>, begin_pos: &'a str) -> Self {
        tts.reverse();
        TTStream(tts, begin_pos)
    }

    pub fn prev_last_pos(&self) -> &'a str {
        self.1
    }

    pub fn peek(&self, index: usize) -> Option<&TT<'a>> {
        let len = self.0.len();
        if index < len {
            unsafe{ Some(self.0.get_unchecked(len - 1 - index)) }
        } else {
            None
        }
    }

    pub fn putback(&mut self, value: TT<'a>) {
        self.1 = &value.1[..0]; // at the begin
        self.0.push(value);
    }

    pub unsafe fn get_unremoved(&self, index: usize) -> Option<TT<'a>> {
        self.peek(index).map(|p| {
            let mut x = uninitialized();
            copy_nonoverlapping(p, &mut x, 1);
            x
        })
    }

    pub fn forget(&mut self, n: usize) {
        struct NonCopy<T>(T); // suppress forget_copy warning (clippy)
        for _ in 0..n {
            match self.next() {
                Some(x) => forget(NonCopy(x)),
                None    => break,
            }
        }
    }
}

impl<'a> Iterator for TTStream<'a> {
    type Item = TT<'a>;

    fn next(&mut self) -> Option<TT<'a>> {
        match self.0.pop() {
            Some((tokk, loc)) => {
                self.1 = &loc[loc.len()..]; // at the end
                Some((tokk, loc))
            },
            None => None,
        }
    }
}

macro_rules! match_eat {
    (@n $s:tt $acc:expr; [$($i:tt)*]) => { $acc };
    (@pat $s:tt $acc:expr; [$($i:tt)*]) => {
        unsafe{ ($($s.get_unremoved($i),)*) }
    };
    (@$f:tt $s:tt $acc:expr; [$($i:tt)*] $pc:tt $($p:tt)*) => {
        match_eat!(@$f $s $acc + 1; [$($i)* $acc] $($p)*)
    };
    ($s:expr; _ => $e_:expr,) => { $e_ };
    ($s:expr; $($p:pat),+ => $e:expr, $($t:tt)*) => {
        match match_eat!(@pat $s 0; [] $($p)*) {
            ($(Some($p),)*) => {
                $s.forget(match_eat!(@n $s 0; [] $($p)*));
                $e
            },
            x => {
                struct NonCopy<T>(T); // suppress forget_copy warning (clippy)
                ::std::mem::forget(NonCopy(x));
                match_eat!($s; $($t)*)
            },
        }
    };
}
