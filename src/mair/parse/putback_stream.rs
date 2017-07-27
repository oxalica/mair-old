//! A stream-like container supporting reading, looking nth ahead and
//! putbacking (unread) elements which will be read next time.

use std::ptr::copy_nonoverlapping;
use std::mem::{uninitialized, forget};

#[derive(Clone)]
pub struct PutbackStream<T>(Vec<T>);

impl<T> PutbackStream<T> {
    pub fn new(mut tts: Vec<T>) -> Self {
        tts.reverse();
        PutbackStream(tts)
    }

    pub fn peek(&self, index: usize) -> Option<&T> {
        let len = self.0.len();
        if index < len {
            unsafe{ Some(self.0.get_unchecked(len - 1 - index)) }
        } else {
            None
        }
    }

    pub fn putback(&mut self, value: T) {
        self.0.push(value);
    }

    pub unsafe fn get_unremoved(&self, index: usize) -> Option<T> {
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

impl<T> Iterator for PutbackStream<T> {
    type Item = T;

    fn next(&mut self) -> Option<T> {
        self.0.pop()
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

#[cfg(test)]
mod test {
    use super::PutbackStream as S;

    #[test]
    fn test_matching() {
        let mut s = S::new(vec![1, 20, 300]);
        let snd = match_eat!{ s;
            2, _ => unreachable!(),
            1, x => x,
            _    => unreachable!(),
        };
        assert_eq!(snd, 20);
        assert_eq!(s.clone().collect::<Vec<_>>(), vec![300]);

        s.putback(44); s.putback(55); s.putback(66);
        assert_eq!(s.clone().collect::<Vec<_>>(), vec![66, 55, 44, 300]);

        match_eat!{ s;
            _, _, _, _, _ => unreachable!(),
            a, 55 => {
                assert_eq!(a, 66);
                assert_eq!(s.clone().collect::<Vec<_>>(), vec![44, 300]);
                assert_eq!(s.peek(1), Some(&300));
                s.putback(0);
                match_eat!{ s;
                    0, 44, 300 => assert!(s.peek(0).is_none()),
                    _          => unreachable!(),
                }
            },
            _ => unreachable!(),
        };
    }
}
