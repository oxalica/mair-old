mod token;
pub use self::token::tokenize;

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
