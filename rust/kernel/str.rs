// SPDX-License-Identifier: GPL-2.0

//! String representations.

use crate::alloc::{flags::*, AllocError, KVec};
use core::fmt::{self, Write};
use core::ops::{Deref, DerefMut};

use crate::error::{code::*, Error};

/// Byte string without UTF-8 validity guarantee.
#[repr(transparent)]
pub struct BStr([u8]);

impl BStr {
    /// Returns the length of this string.
    #[inline]
    pub const fn len(&self) -> usize {
        self.0.len()
    }

    /// Returns `true` if the string is empty.
    #[inline]
    pub const fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Creates a [`BStr`] from a `[u8]`.
    #[inline]
    pub const fn from_bytes(bytes: &[u8]) -> &Self {
        // SAFETY: `BStr` is transparent to `[u8]`.
        unsafe { &*(bytes as *const [u8] as *const BStr) }
    }

    /// Returns an object that implements [`Display`] for safely printing a [`BStr`] that may
    /// contain non-Unicode data. If you would like an implementation which escapes the [`BStr`]
    /// please use [`Debug`] instead.
    ///
    /// [`Display`]: fmt::Display
    /// [`Debug`]: fmt::Debug
    ///
    /// # Examples
    ///
    /// ```
    /// # use kernel::{fmt, b_str, str::CString};
    /// let ascii = b_str!("Hello, BStr!");
    /// let s = CString::try_from_fmt(fmt!("{}", ascii.display()))?;
    /// assert_eq!(s.to_bytes(), "Hello, BStr!".as_bytes());
    ///
    /// let non_ascii = b_str!("🦀");
    /// let s = CString::try_from_fmt(fmt!("{}", non_ascii.display()))?;
    /// assert_eq!(s.to_bytes(), "\\xf0\\x9f\\xa6\\x80".as_bytes());
    /// # Ok::<(), kernel::error::Error>(())
    /// ```
    #[inline]
    pub fn display(&self) -> Display<'_> {
        Display {
            inner: self,
            escape_common: true,
        }
    }
}

/// Helper struct for safely printing a [`BStr`] with [`fmt!`] and `{}`.
///
/// A [`BStr`] might contain non-Unicode data. This `struct` implements the [`Display`] trait in a
/// way that mitigates that. It is created by the [`display`](BStr::display) method on [`BStr`].
///
/// If you would like an implementation which escapes the string please use [`Debug`] instead.
///
/// # Examples
///
/// ```
/// # use kernel::{fmt, b_str, str::CString};
/// let ascii = b_str!("Hello, BStr!");
/// let s = CString::try_from_fmt(fmt!("{}", ascii.display()))?;
/// assert_eq!(s.to_bytes(), "Hello, BStr!".as_bytes());
///
/// let non_ascii = b_str!("🦀");
/// let s = CString::try_from_fmt(fmt!("{}", non_ascii.display()))?;
/// assert_eq!(s.to_bytes(), "\\xf0\\x9f\\xa6\\x80".as_bytes());
/// # Ok::<(), kernel::error::Error>(())
/// ```
///
/// [`fmt!`]: crate::fmt
/// [`Debug`]: fmt::Debug
/// [`Display`]: fmt::Display
pub struct Display<'a> {
    inner: &'a BStr,
    escape_common: bool,
}

impl fmt::Display for Display<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Self {
            inner: BStr(b),
            escape_common,
        } = self;
        for &b in b {
            match b {
                // Common escape codes.
                b'\t' if *escape_common => f.write_str("\\t")?,
                b'\n' if *escape_common => f.write_str("\\n")?,
                b'\r' if *escape_common => f.write_str("\\r")?,
                // Printable characters.
                0x20..=0x7e => f.write_char(b as char)?,
                _ => write!(f, "\\x{:02x}", b)?,
            }
        }
        Ok(())
    }
}

impl fmt::Debug for BStr {
    /// Formats printable ASCII characters with a double quote on either end,
    /// escaping the rest.
    ///
    /// ```
    /// # use kernel::{fmt, b_str, str::CString};
    /// // Embedded double quotes are escaped.
    /// let ascii = b_str!("Hello, \"BStr\"!");
    /// let s = CString::try_from_fmt(fmt!("{:?}", ascii))?;
    /// assert_eq!(s.to_bytes(), "\"Hello, \\\"BStr\\\"!\"".as_bytes());
    ///
    /// let non_ascii = b_str!("😺");
    /// let s = CString::try_from_fmt(fmt!("{:?}", non_ascii))?;
    /// assert_eq!(s.to_bytes(), "\"\\xf0\\x9f\\x98\\xba\"".as_bytes());
    /// # Ok::<(), kernel::error::Error>(())
    /// ```
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_char('"')?;
        for &b in &self.0 {
            match b {
                // Common escape codes.
                b'\t' => f.write_str("\\t")?,
                b'\n' => f.write_str("\\n")?,
                b'\r' => f.write_str("\\r")?,
                // String escape characters.
                b'\"' => f.write_str("\\\"")?,
                b'\\' => f.write_str("\\\\")?,
                // Printable characters.
                0x20..=0x7e => f.write_char(b as char)?,
                _ => write!(f, "\\x{:02x}", b)?,
            }
        }
        f.write_char('"')
    }
}

impl Deref for BStr {
    type Target = [u8];

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

/// Creates a new [`BStr`] from a string literal.
///
/// `b_str!` converts the supplied string literal to byte string, so non-ASCII
/// characters can be included.
///
/// # Examples
///
/// ```
/// # use kernel::b_str;
/// # use kernel::str::BStr;
/// const MY_BSTR: &BStr = b_str!("My awesome BStr!");
/// ```
#[macro_export]
macro_rules! b_str {
    ($str:literal) => {{
        const S: &'static str = $str;
        const C: &'static $crate::str::BStr = $crate::str::BStr::from_bytes(S.as_bytes());
        C
    }};
}

pub use core::ffi::CStr;

/// Returns a C pointer to the string.
// It is a free function rather than a method on an extension trait because:
//
// - error[E0379]: functions in trait impls cannot be declared const
#[inline]
pub const fn as_char_ptr_in_const_context(c_str: &CStr) -> *const crate::ffi::c_char {
    c_str.as_ptr().cast()
}

/// Extensions to [`CStr`].
pub trait CStrExt {
    /// Wraps a raw C string pointer.
    ///
    /// # Safety
    ///
    /// `ptr` must be a valid pointer to a `NUL`-terminated C string, and it must
    /// last at least `'a`. When `CStr` is alive, the memory pointed by `ptr`
    /// must not be mutated.
    // This function exists to paper over the fact that `CStr::from_ptr` takes a `*const
    // core::ffi::c_char` rather than a `*const crate::ffi::c_char`.
    unsafe fn from_char_ptr<'a>(ptr: *const crate::ffi::c_char) -> &'a Self;

    /// Creates a mutable [`CStr`] from a `[u8]` without performing any
    /// additional checks.
    ///
    /// # Safety
    ///
    /// `bytes` *must* end with a `NUL` byte, and should only have a single
    /// `NUL` byte (or the string will be truncated).
    unsafe fn from_bytes_with_nul_unchecked_mut(bytes: &mut [u8]) -> &mut Self;

    /// Returns a C pointer to the string.
    // This function exists to paper over the fact that `CStr::as_ptr` returns a `*const
    // core::ffi::c_char` rather than a `*const crate::ffi::c_char`.
    fn as_char_ptr(&self) -> *const crate::ffi::c_char;

    /// Convert this [`CStr`] into a [`CString`] by allocating memory and
    /// copying over the string data.
    fn to_cstring(&self) -> Result<CString, AllocError>;

    /// Converts this [`CStr`] to its ASCII lower case equivalent in-place.
    ///
    /// ASCII letters 'A' to 'Z' are mapped to 'a' to 'z',
    /// but non-ASCII letters are unchanged.
    ///
    /// To return a new lowercased value without modifying the existing one, use
    /// [`to_ascii_lowercase()`].
    ///
    /// [`to_ascii_lowercase()`]: #method.to_ascii_lowercase
    fn make_ascii_lowercase(&mut self);

    /// Converts this [`CStr`] to its ASCII upper case equivalent in-place.
    ///
    /// ASCII letters 'a' to 'z' are mapped to 'A' to 'Z',
    /// but non-ASCII letters are unchanged.
    ///
    /// To return a new uppercased value without modifying the existing one, use
    /// [`to_ascii_uppercase()`].
    ///
    /// [`to_ascii_uppercase()`]: #method.to_ascii_uppercase
    fn make_ascii_uppercase(&mut self);

    /// Returns a copy of this [`CString`] where each character is mapped to its
    /// ASCII lower case equivalent.
    ///
    /// ASCII letters 'A' to 'Z' are mapped to 'a' to 'z',
    /// but non-ASCII letters are unchanged.
    ///
    /// To lowercase the value in-place, use [`make_ascii_lowercase`].
    ///
    /// [`make_ascii_lowercase`]: str::make_ascii_lowercase
    fn to_ascii_lowercase(&self) -> Result<CString, AllocError>;

    /// Returns a copy of this [`CString`] where each character is mapped to its
    /// ASCII upper case equivalent.
    ///
    /// ASCII letters 'a' to 'z' are mapped to 'A' to 'Z',
    /// but non-ASCII letters are unchanged.
    ///
    /// To uppercase the value in-place, use [`make_ascii_uppercase`].
    ///
    /// [`make_ascii_uppercase`]: str::make_ascii_uppercase
    fn to_ascii_uppercase(&self) -> Result<CString, AllocError>;

    /// Returns an object that implements [`Display`] for safely printing a [`CStr`] that may
    /// contain non-Unicode data. If you would like an implementation which escapes the [`CStr`]
    /// please use [`Debug`] instead.
    ///
    /// [`Display`]: fmt::Display
    /// [`Debug`]: fmt::Debug
    ///
    /// # Examples
    ///
    /// ```
    /// # use kernel::fmt;
    /// # use kernel::str::CString;
    /// let penguin = c"🐧";
    /// let s = CString::try_from_fmt(fmt!("{}", penguin.display()))?;
    /// assert_eq!(s.to_bytes_with_nul(), "\\xf0\\x9f\\x90\\xa7\0".as_bytes());
    ///
    /// let ascii = c"so \"cool\"";
    /// let s = CString::try_from_fmt(fmt!("{}", ascii.display()))?;
    /// assert_eq!(s.to_bytes_with_nul(), "so \"cool\"\0".as_bytes());
    /// # Ok::<(), kernel::error::Error>(())
    /// ```
    fn display(&self) -> Display<'_>;
}

/// Converts a mutable C string to a mutable byte slice.
///
/// # Safety
///
/// The caller must ensure that the slice ends in a NUL byte and contains no other NUL bytes before
/// the borrow ends and the underlying [`CStr`] is used.
unsafe fn to_bytes_mut(s: &mut CStr) -> &mut [u8] {
    // SAFETY: the cast from `&CStr` to `&[u8]` is safe since `CStr` has the same layout as `&[u8]`
    // (this is technically not guaranteed, but we rely on it here). The pointer dereference is
    // safe since it comes from a mutable reference which is guaranteed to be valid for writes.
    unsafe { &mut *(s as *mut CStr as *mut [u8]) }
}

impl CStrExt for CStr {
    #[inline]
    unsafe fn from_char_ptr<'a>(ptr: *const crate::ffi::c_char) -> &'a Self {
        // SAFETY: The safety preconditions are the same as for `CStr::from_ptr`.
        unsafe { CStr::from_ptr(ptr.cast()) }
    }

    #[inline]
    unsafe fn from_bytes_with_nul_unchecked_mut(bytes: &mut [u8]) -> &mut Self {
        // SAFETY: the cast from `&[u8]` to `&CStr` is safe since the properties of `bytes` are
        // guaranteed by the safety precondition and `CStr` has the same layout as `&[u8]` (this is
        // technically not guaranteed, but we rely on it here). The pointer dereference is safe
        // since it comes from a mutable reference which is guaranteed to be valid for writes.
        unsafe { &mut *(bytes as *mut [u8] as *mut CStr) }
    }

    #[inline]
    fn as_char_ptr(&self) -> *const crate::ffi::c_char {
        self.as_ptr().cast()
    }

    fn to_cstring(&self) -> Result<CString, AllocError> {
        CString::try_from(self)
    }

    fn make_ascii_lowercase(&mut self) {
        // SAFETY: This doesn't introduce or remove NUL bytes in the C string.
        unsafe { to_bytes_mut(self) }.make_ascii_lowercase();
    }

    fn make_ascii_uppercase(&mut self) {
        // SAFETY: This doesn't introduce or remove NUL bytes in the C string.
        unsafe { to_bytes_mut(self) }.make_ascii_uppercase();
    }

    fn to_ascii_lowercase(&self) -> Result<CString, AllocError> {
        let mut s = self.to_cstring()?;

        s.make_ascii_lowercase();

        Ok(s)
    }

    fn to_ascii_uppercase(&self) -> Result<CString, AllocError> {
        let mut s = self.to_cstring()?;

        s.make_ascii_uppercase();

        Ok(s)
    }

    #[inline]
    fn display(&self) -> Display<'_> {
        Display {
            inner: self.as_ref(),
            escape_common: false,
        }
    }
}

impl AsRef<BStr> for CStr {
    #[inline]
    fn as_ref(&self) -> &BStr {
        BStr::from_bytes(self.to_bytes())
    }
}

/// Creates a static C string wrapper at compile time.
///
/// Rust supports C string literals since Rust 1.77, and they should be used instead of this macro
/// where possible. This macro exists to allow static *non-literal* C strings to be created at
/// compile time. This is most often used in other macros.
///
/// # Panics
///
/// This macro panics if the operand contains an interior `NUL` byte.
///
/// # Examples
///
/// ```
/// # use kernel::c_str_avoid_literals;
/// # use kernel::str::CStr;
/// const MY_CSTR: &CStr = c_str_avoid_literals!(concat!(file!(), ":", line!(), ": My CStr!"));
/// ```
#[macro_export]
macro_rules! c_str_avoid_literals {
    // NB: we could write `($str:lit) => compile_error!("use a C string literal instead");` here but
    // that would trigger when the literal is at the top of several macro expansions. That would be
    // too limiting to macro authors, so we rely on the name as a hint instead.
    ($str:expr) => {{
        const S: &'static str = concat!($str, "\0");
        const C: &'static $crate::str::CStr =
            match $crate::str::CStr::from_bytes_with_nul(S.as_bytes()) {
                Ok(v) => v,
                Err(core::ffi::FromBytesWithNulError { .. }) => {
                    panic!("string contains interior NUL")
                }
            };
        C
    }};
}

#[cfg(test)]
#[expect(clippy::items_after_test_module)]
mod tests {
    use super::*;

    struct String(CString);

    impl String {
        fn from_fmt(args: fmt::Arguments<'_>) -> Self {
            String(CString::try_from_fmt(args).unwrap())
        }
    }

    impl Deref for String {
        type Target = str;

        fn deref(&self) -> &str {
            self.0.to_str().unwrap()
        }
    }

    macro_rules! format {
        ($($f:tt)*) => ({
            &*String::from_fmt(kernel::fmt!($($f)*))
        })
    }

    const ALL_ASCII_CHARS: &str =
        "\\x01\\x02\\x03\\x04\\x05\\x06\\x07\\x08\\x09\\x0a\\x0b\\x0c\\x0d\\x0e\\x0f\
        \\x10\\x11\\x12\\x13\\x14\\x15\\x16\\x17\\x18\\x19\\x1a\\x1b\\x1c\\x1d\\x1e\\x1f \
        !\"#$%&'()*+,-./0123456789:;<=>?@\
        ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`abcdefghijklmnopqrstuvwxyz{|}~\\x7f\
        \\x80\\x81\\x82\\x83\\x84\\x85\\x86\\x87\\x88\\x89\\x8a\\x8b\\x8c\\x8d\\x8e\\x8f\
        \\x90\\x91\\x92\\x93\\x94\\x95\\x96\\x97\\x98\\x99\\x9a\\x9b\\x9c\\x9d\\x9e\\x9f\
        \\xa0\\xa1\\xa2\\xa3\\xa4\\xa5\\xa6\\xa7\\xa8\\xa9\\xaa\\xab\\xac\\xad\\xae\\xaf\
        \\xb0\\xb1\\xb2\\xb3\\xb4\\xb5\\xb6\\xb7\\xb8\\xb9\\xba\\xbb\\xbc\\xbd\\xbe\\xbf\
        \\xc0\\xc1\\xc2\\xc3\\xc4\\xc5\\xc6\\xc7\\xc8\\xc9\\xca\\xcb\\xcc\\xcd\\xce\\xcf\
        \\xd0\\xd1\\xd2\\xd3\\xd4\\xd5\\xd6\\xd7\\xd8\\xd9\\xda\\xdb\\xdc\\xdd\\xde\\xdf\
        \\xe0\\xe1\\xe2\\xe3\\xe4\\xe5\\xe6\\xe7\\xe8\\xe9\\xea\\xeb\\xec\\xed\\xee\\xef\
        \\xf0\\xf1\\xf2\\xf3\\xf4\\xf5\\xf6\\xf7\\xf8\\xf9\\xfa\\xfb\\xfc\\xfd\\xfe\\xff";

    #[test]
    fn test_cstr_to_str() {
        let good_bytes = b"\xf0\x9f\xa6\x80\0";
        let checked_cstr = CStr::from_bytes_with_nul(good_bytes).unwrap();
        let checked_str = checked_cstr.to_str().unwrap();
        assert_eq!(checked_str, "🦀");
    }

    #[test]
    #[should_panic]
    fn test_cstr_to_str_panic() {
        let bad_bytes = b"\xc3\x28\0";
        let checked_cstr = CStr::from_bytes_with_nul(bad_bytes).unwrap();
        checked_cstr.to_str().unwrap();
    }

    #[test]
    fn test_cstr_display() {
        assert_eq!(format!("{}", c"hello, world!".display()), "hello, world!");
        assert_eq!(format!("{}", c"\x01\x09\x0a".display()), "\\x01\\x09\\x0a");
        assert_eq!(format!("{}", c"d\xe9j\xe0 vu".display()), "d\\xe9j\\xe0 vu");
        assert_eq!(
            format!("{}", c"\xf0\x9f\xa6\x80".display()),
            "\\xf0\\x9f\\xa6\\x80"
        );
    }

    #[test]
    fn test_cstr_display_all_bytes() {
        let mut bytes: [u8; 256] = [0; 256];
        // fill `bytes` with [1..=255] + [0]
        for i in u8::MIN..=u8::MAX {
            bytes[i as usize] = i.wrapping_add(1);
        }
        let cstr = CStr::from_bytes_with_nul(&bytes).unwrap();
        assert_eq!(format!("{}", cstr.display()), ALL_ASCII_CHARS);
    }

    #[test]
    fn test_cstr_debug() {
        assert_eq!(format!("{:?}", c"hello, world!"), "\"hello, world!\"");
        assert_eq!(format!("{:?}", c"\x01\x09\x0a"), "\"\\x01\\t\\n\"");
        assert_eq!(format!("{:?}", c"d\xe9j\xe0 vu"), "\"d\\xe9j\\xe0 vu\"");
        assert_eq!(
            format!("{:?}", c"\xf0\x9f\xa6\x80"),
            "\"\\xf0\\x9f\\xa6\\x80\""
        );
    }

    #[test]
    fn test_bstr_display() {
        let hello_world = BStr::from_bytes(b"hello, world!");
        assert_eq!(format!("{}", hello_world.display()), "hello, world!");
        let escapes = BStr::from_bytes(b"_\t_\n_\r_\\_\'_\"_");
        assert_eq!(format!("{}", escapes.display()), "_\\t_\\n_\\r_\\_'_\"_");
        let others = BStr::from_bytes(b"\x01");
        assert_eq!(format!("{}", others.display()), "\\x01");
        let non_ascii = BStr::from_bytes(b"d\xe9j\xe0 vu");
        assert_eq!(format!("{}", non_ascii.display()), "d\\xe9j\\xe0 vu");
        let good_bytes = BStr::from_bytes(b"\xf0\x9f\xa6\x80");
        assert_eq!(format!("{}", good_bytes.display()), "\\xf0\\x9f\\xa6\\x80");
    }

    #[test]
    fn test_bstr_debug() {
        let hello_world = BStr::from_bytes(b"hello, world!");
        assert_eq!(format!("{:?}", hello_world), "\"hello, world!\"");
        let escapes = BStr::from_bytes(b"_\t_\n_\r_\\_\'_\"_");
        assert_eq!(format!("{:?}", escapes), "\"_\\t_\\n_\\r_\\\\_'_\\\"_\"");
        let others = BStr::from_bytes(b"\x01");
        assert_eq!(format!("{:?}", others), "\"\\x01\"");
        let non_ascii = BStr::from_bytes(b"d\xe9j\xe0 vu");
        assert_eq!(format!("{:?}", non_ascii), "\"d\\xe9j\\xe0 vu\"");
        let good_bytes = BStr::from_bytes(b"\xf0\x9f\xa6\x80");
        assert_eq!(format!("{:?}", good_bytes), "\"\\xf0\\x9f\\xa6\\x80\"");
    }
}

/// Allows formatting of [`fmt::Arguments`] into a raw buffer.
///
/// It does not fail if callers write past the end of the buffer so that they can calculate the
/// size required to fit everything.
///
/// # Invariants
///
/// The memory region between `pos` (inclusive) and `end` (exclusive) is valid for writes if `pos`
/// is less than `end`.
pub(crate) struct RawFormatter {
    // Use `usize` to use `saturating_*` functions.
    beg: usize,
    pos: usize,
    end: usize,
}

impl RawFormatter {
    /// Creates a new instance of [`RawFormatter`] with an empty buffer.
    fn new() -> Self {
        // INVARIANT: The buffer is empty, so the region that needs to be writable is empty.
        Self {
            beg: 0,
            pos: 0,
            end: 0,
        }
    }

    /// Creates a new instance of [`RawFormatter`] with the given buffer pointers.
    ///
    /// # Safety
    ///
    /// If `pos` is less than `end`, then the region between `pos` (inclusive) and `end`
    /// (exclusive) must be valid for writes for the lifetime of the returned [`RawFormatter`].
    pub(crate) unsafe fn from_ptrs(pos: *mut u8, end: *mut u8) -> Self {
        // INVARIANT: The safety requirements guarantee the type invariants.
        Self {
            beg: pos as _,
            pos: pos as _,
            end: end as _,
        }
    }

    /// Creates a new instance of [`RawFormatter`] with the given buffer.
    ///
    /// # Safety
    ///
    /// The memory region starting at `buf` and extending for `len` bytes must be valid for writes
    /// for the lifetime of the returned [`RawFormatter`].
    pub(crate) unsafe fn from_buffer(buf: *mut u8, len: usize) -> Self {
        let pos = buf as usize;
        // INVARIANT: We ensure that `end` is never less then `buf`, and the safety requirements
        // guarantees that the memory region is valid for writes.
        Self {
            pos,
            beg: pos,
            end: pos.saturating_add(len),
        }
    }

    /// Returns the current insert position.
    ///
    /// N.B. It may point to invalid memory.
    pub(crate) fn pos(&self) -> *mut u8 {
        self.pos as _
    }

    /// Returns the number of bytes written to the formatter.
    pub(crate) fn bytes_written(&self) -> usize {
        self.pos - self.beg
    }
}

impl fmt::Write for RawFormatter {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        // `pos` value after writing `len` bytes. This does not have to be bounded by `end`, but we
        // don't want it to wrap around to 0.
        let pos_new = self.pos.saturating_add(s.len());

        // Amount that we can copy. `saturating_sub` ensures we get 0 if `pos` goes past `end`.
        let len_to_copy = core::cmp::min(pos_new, self.end).saturating_sub(self.pos);

        if len_to_copy > 0 {
            // SAFETY: If `len_to_copy` is non-zero, then we know `pos` has not gone past `end`
            // yet, so it is valid for write per the type invariants.
            unsafe {
                core::ptr::copy_nonoverlapping(
                    s.as_bytes().as_ptr(),
                    self.pos as *mut u8,
                    len_to_copy,
                )
            };
        }

        self.pos = pos_new;
        Ok(())
    }
}

/// Allows formatting of [`fmt::Arguments`] into a raw buffer.
///
/// Fails if callers attempt to write more than will fit in the buffer.
pub(crate) struct Formatter(RawFormatter);

impl Formatter {
    /// Creates a new instance of [`Formatter`] with the given buffer.
    ///
    /// # Safety
    ///
    /// The memory region starting at `buf` and extending for `len` bytes must be valid for writes
    /// for the lifetime of the returned [`Formatter`].
    pub(crate) unsafe fn from_buffer(buf: *mut u8, len: usize) -> Self {
        // SAFETY: The safety requirements of this function satisfy those of the callee.
        Self(unsafe { RawFormatter::from_buffer(buf, len) })
    }
}

impl Deref for Formatter {
    type Target = RawFormatter;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl fmt::Write for Formatter {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        self.0.write_str(s)?;

        // Fail the request if we go past the end of the buffer.
        if self.0.pos > self.0.end {
            Err(fmt::Error)
        } else {
            Ok(())
        }
    }
}

/// An owned string that is guaranteed to have exactly one `NUL` byte, which is at the end.
///
/// Used for interoperability with kernel APIs that take C strings.
///
/// # Invariants
///
/// The string is always `NUL`-terminated and contains no other `NUL` bytes.
///
/// # Examples
///
/// ```
/// use kernel::{fmt, str::CString};
///
/// let s = CString::try_from_fmt(fmt!("{}{}{}", "abc", 10, 20))?;
/// assert_eq!(s.to_bytes_with_nul(), "abc1020\0".as_bytes());
///
/// let tmp = "testing";
/// let s = CString::try_from_fmt(fmt!("{tmp}{}", 123))?;
/// assert_eq!(s.to_bytes_with_nul(), "testing123\0".as_bytes());
///
/// // This fails because it has an embedded `NUL` byte.
/// let s = CString::try_from_fmt(fmt!("a\0b{}", 123));
/// assert_eq!(s.is_ok(), false);
/// # Ok::<(), kernel::error::Error>(())
/// ```
pub struct CString {
    buf: KVec<u8>,
}

impl CString {
    /// Creates an instance of [`CString`] from the given formatted arguments.
    pub fn try_from_fmt(args: fmt::Arguments<'_>) -> Result<Self, Error> {
        // Calculate the size needed (formatted string plus `NUL` terminator).
        let mut f = RawFormatter::new();
        f.write_fmt(args)?;
        f.write_str("\0")?;
        let size = f.bytes_written();

        // Allocate a vector with the required number of bytes, and write to it.
        let mut buf = KVec::with_capacity(size, GFP_KERNEL)?;
        // SAFETY: The buffer stored in `buf` is at least of size `size` and is valid for writes.
        let mut f = unsafe { Formatter::from_buffer(buf.as_mut_ptr(), size) };
        f.write_fmt(args)?;
        f.write_str("\0")?;

        // SAFETY: The number of bytes that can be written to `f` is bounded by `size`, which is
        // `buf`'s capacity. The contents of the buffer have been initialised by writes to `f`.
        unsafe { buf.set_len(f.bytes_written()) };

        // Check that there are no `NUL` bytes before the end.
        // SAFETY: The buffer is valid for read because `f.bytes_written()` is bounded by `size`
        // (which the minimum buffer size) and is non-zero (we wrote at least the `NUL` terminator)
        // so `f.bytes_written() - 1` doesn't underflow.
        let ptr = unsafe { bindings::memchr(buf.as_ptr().cast(), 0, f.bytes_written() - 1) };
        if !ptr.is_null() {
            return Err(EINVAL);
        }

        // INVARIANT: We wrote the `NUL` terminator and checked above that no other `NUL` bytes
        // exist in the buffer.
        Ok(Self { buf })
    }
}

impl Deref for CString {
    type Target = CStr;

    fn deref(&self) -> &Self::Target {
        // SAFETY: The type invariants guarantee that the string is `NUL`-terminated and that no
        // other `NUL` bytes exist.
        unsafe { CStr::from_bytes_with_nul_unchecked(self.buf.as_slice()) }
    }
}

impl DerefMut for CString {
    fn deref_mut(&mut self) -> &mut Self::Target {
        // SAFETY: A `CString` is always NUL-terminated and contains no other
        // NUL bytes.
        unsafe { CStr::from_bytes_with_nul_unchecked_mut(self.buf.as_mut_slice()) }
    }
}

impl<'a> TryFrom<&'a CStr> for CString {
    type Error = AllocError;

    fn try_from(cstr: &'a CStr) -> Result<CString, AllocError> {
        let mut buf = KVec::new();

        buf.extend_from_slice(cstr.to_bytes_with_nul(), GFP_KERNEL)?;

        // INVARIANT: The `CStr` and `CString` types have the same invariants for
        // the string data, and we copied it over without changes.
        Ok(CString { buf })
    }
}

impl fmt::Debug for CString {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&**self, f)
    }
}

/// A convenience alias for [`core::format_args`].
#[macro_export]
macro_rules! fmt {
    ($($f:tt)*) => ( core::format_args!($($f)*) )
}
