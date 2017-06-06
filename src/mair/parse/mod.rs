pub mod ast;
pub mod lexer;
pub mod grammar;

/// Get item offset of b from a, similar to pointer subtraction
/// `(const T *)a - (const T *)b` in C/C++.
///
/// If the arguments are not in the same block of memory(`[T]`, `Vec<T>`, etc.),
/// the return value is unpredictable and meaningless.
///
/// # Example
/// It's useful to get start address of a slice in the source of it.
///
/// ```
/// use mair::parse::ptr_diff;
/// let s = [1, 2, 3, 4, 5];
/// let s1 = &s[1..];
/// let s2 = &s1[2..3];
/// assert_eq!(ptr_diff(s.as_ptr(), s.as_ptr()), 0);
/// assert_eq!(ptr_diff(s1.as_ptr(), s.as_ptr()), 1);
/// assert_eq!(ptr_diff(s2.as_ptr(), s.as_ptr()), 3);
/// assert_eq!(ptr_diff(s1.as_ptr(), s2.as_ptr()), -2);
/// ```
pub fn ptr_diff<T>(a: *const T, b: *const T) -> isize {
    use std::mem::size_of;
    (a as isize - b as isize) / size_of::<T>() as isize
}

/// The same as `ptr_diff()` but for `&str`.
pub fn str_ptr_diff(a: &str, b: &str) -> isize {
    ptr_diff(a.as_ptr(), b.as_ptr())
}

/// Generate a map from character indices to line and column numbers,
///   including the position next to the end of input (EOI).
///
/// # Example
///
/// ```
/// use mair::parse::gen_position_map;
/// let s1 = "ab\ncd\r\nde";
/// let s2 = "\n!\r\n\n";
/// assert_eq!(gen_position_map(s1), vec![
///     (1, 1), (1, 2), (1, 3),
///     (2, 1), (2, 2), (2, 3), (2, 4),
///     (3, 1), (3, 2),
///     (4, 1),
/// ]);
/// assert_eq!(gen_position_map(s2), vec![
///     (1, 1),
///     (2, 1), (2, 2), (2, 3),
///     (3, 1),
///     (4, 1),
/// ]);
/// ```
pub fn gen_position_map(s: &str) -> Vec<(usize, usize)> {
    let mut v = vec![(0, 0); s.len()];
    let mut lastline = 0;
    for (i, line) in s.lines().enumerate() {
        let begin = ptr_diff(line.as_ptr(), s.as_ptr()) as usize;
        lastline = i + 1;
        for j in 0..line.len()+2 { // if ends with `\r\n`
            v.get_mut(begin + j).map(|c| *c = (i + 1, j + 1));
        }
    }
    v.push((lastline + 1, 1));
    v
}
