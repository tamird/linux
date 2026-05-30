// SPDX-License-Identifier: GPL-2.0
// Copyright (C) 2025 Google LLC.

use super::{
    BinaryReader,
    BinaryWriter,
    ReadCallback,
    ReadWriteCallbacks,
    Reader,
    WriteCallback,
    Writer, //
};

use crate::{
    fmt,
    fs::file,
    prelude::*,
    seq_file::SeqFile,
    seq_print,
    uaccess::UserSlice, //
};

use core::marker::PhantomData;

#[cfg(CONFIG_DEBUG_FS)]
use core::ops::Deref;

/// # Invariant
///
/// The callbacks in `operations` obey the following requirements:
///
/// * A callback which reads a pointer derived from the private-data pointer
///   registered for a file reads it only as a shared reference to `T`.
/// * A callback which reads the auxiliary-data pointer registered for a file
///   reads it only as a shared reference to `A`.
/// * A callback which may run after the file has been removed does not access
///   either pointer.
pub(super) struct FileOps<T, A = ()> {
    #[cfg(CONFIG_DEBUG_FS)]
    operations: bindings::file_operations,
    #[cfg(CONFIG_DEBUG_FS)]
    mode: u16,
    _phantom: PhantomData<(T, A)>,
}

impl<T, A> FileOps<T, A> {
    /// # Safety
    ///
    /// Each callback in `operations` which reads a pointer derived from the
    /// registered private-data or auxiliary-data pointer must read it only as
    /// a shared reference to `T` or `A`, respectively. Callbacks which may run
    /// after the file has been removed must not access either pointer.
    const unsafe fn new(operations: bindings::file_operations, mode: u16) -> Self {
        Self {
            #[cfg(CONFIG_DEBUG_FS)]
            operations,
            #[cfg(CONFIG_DEBUG_FS)]
            mode,
            _phantom: PhantomData,
        }
    }
    #[cfg(CONFIG_DEBUG_FS)]
    pub(crate) const fn mode(&self) -> u16 {
        self.mode
    }
}

#[cfg(CONFIG_DEBUG_FS)]
impl<T, A> Deref for FileOps<T, A> {
    type Target = bindings::file_operations;

    fn deref(&self) -> &Self::Target {
        &self.operations
    }
}

struct WriterAdapter<T>(T);

impl<'a, T: Writer> fmt::Display for WriterAdapter<&'a T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.write(f)
    }
}

/// Implements `open` for `file_operations` via `single_open` to fill out a `seq_file`.
///
/// # Safety
///
/// * `inode`'s private pointer may be stored for use by the resulting file
///   operations and must be valid to convert into a shared reference to `T`
///   whenever those operations access it. No unique reference may alias it
///   during such access.
/// * `file` must point to a live, not-yet-initialized file object.
unsafe extern "C" fn writer_open<T: Writer + Sync>(
    inode: *mut bindings::inode,
    file: *mut bindings::file,
) -> c_int {
    // SAFETY: The caller ensures that `inode` is a valid pointer.
    let data = unsafe { (*inode).i_private };
    // SAFETY:
    // * `file` is acceptable by caller precondition.
    // * `writer_act` will be called as a seq-file show callback with private data set to the
    //   third argument, so we meet its safety requirements.
    // * The `data` pointer passed in the third argument is valid whenever
    //   `writer_act` uses it by caller preconditions.
    unsafe { bindings::single_open(file, Some(writer_act::<T>), data) }
}

/// Prints private data stashed in a seq_file to that seq file.
///
/// # Safety
///
/// `seq` must point to a live `seq_file`. No other thread may access any field
/// except by reading `private` during the call. Its private data must be a
/// valid pointer to a `T` which may not have any unique references alias it
/// during the call.
unsafe extern "C" fn writer_act<T: Writer + Sync>(
    seq: *mut bindings::seq_file,
    _: *mut c_void,
) -> c_int {
    // SAFETY: By caller precondition, this pointer is valid pointer to a `T`, and
    // there are not and will not be any unique references until we are done.
    let data = unsafe { &*((*seq).private.cast::<T>()) };
    // SAFETY: By caller precondition, concurrent accesses to `seq` only read
    // `private`.
    let seq_file = unsafe { SeqFile::from_raw(seq) };
    seq_print!(seq_file, "{}", WriterAdapter(data));
    0
}

// Work around lack of generic const items.
pub(crate) trait ReadFile<T> {
    const FILE_OPS: FileOps<T>;
}

impl<T: Writer + Sync> ReadFile<T> for T {
    const FILE_OPS: FileOps<T> = {
        let operations = bindings::file_operations {
            read: Some(bindings::seq_read),
            llseek: Some(bindings::seq_lseek),
            release: Some(bindings::single_release),
            open: Some(writer_open::<Self>),
            ..pin_init::zeroed()
        };
        // SAFETY: `writer_open` stores the inode's `T` pointer for
        // `writer_act`, which uses it only from `read` and `llseek`; debugfs
        // protects both operations against removal. `single_release` does not
        // access it.
        unsafe { FileOps::new(operations, 0o400) }
    };
}

trait FormatCallback<D> {
    fn format(&self, data: &D, formatter: &mut fmt::Formatter<'_>) -> fmt::Result;
}

impl<D> FormatCallback<D> for ReadCallback<D> {
    fn format(&self, data: &D, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        self(data, formatter)
    }
}

impl<D> FormatCallback<D> for ReadWriteCallbacks<D> {
    fn format(&self, data: &D, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        (self.read)(data, formatter)
    }
}

/// Formats data through a retained callback.
struct CallbackWriter<'a, D, C> {
    data: &'a D,
    callback: &'a C,
}

impl<D, C> fmt::Display for CallbackWriter<'_, D, C>
where
    C: FormatCallback<D>,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.callback.format(self.data, f)
    }
}

/// Implements `open` for read-callback operations via `single_open`.
///
/// # Safety
///
/// * `inode`'s private pointer may be stored for use by the resulting file
///   operations and must be valid to convert into a shared reference to `D`
///   whenever those operations access it. No unique reference may alias it
///   during such access.
/// * `file` must point to a live, not-yet-initialized file object whose
///   auxiliary data is valid to convert into a shared reference to callback
///   data of type `C` whenever the resulting file operations access it.
unsafe extern "C" fn callback_writer_open<D, C>(
    inode: *mut bindings::inode,
    file: *mut bindings::file,
) -> c_int
where
    D: Sync,
    C: FormatCallback<D> + Sync,
{
    // SAFETY: The caller ensures that `inode` is a valid pointer.
    let data = unsafe { (*inode).i_private };
    // SAFETY:
    // * `file` is acceptable by caller precondition.
    // * `callback_writer_act` will be called as a seq-file show callback associated
    //   with `file` and with private data set to the third argument.
    // * The `data` pointer passed in the third argument is valid whenever
    //   `callback_writer_act` uses it by caller preconditions.
    unsafe { bindings::single_open(file, Some(callback_writer_act::<D, C>), data) }
}

/// Prints data through a read callback to a seq file.
///
/// # Safety
///
/// * `seq` must point to a live `seq_file`. No other thread may access any
///   field except by reading `private` during the call. Its private data must
///   be a valid pointer to a `D` which may not have any unique references
///   alias it during the call.
/// * `seq` must be associated with a file whose auxiliary data is valid to
///   convert to a shared reference to callback data of type `C` during the call.
unsafe extern "C" fn callback_writer_act<D, C>(
    seq: *mut bindings::seq_file,
    _: *mut c_void,
) -> c_int
where
    D: Sync,
    C: FormatCallback<D> + Sync,
{
    // SAFETY: By caller precondition, this pointer is a valid pointer to a `D`,
    // and there are not and will not be any unique references until we are done.
    let data = unsafe { &*((*seq).private.cast::<D>()) };
    // SAFETY: By caller precondition, the auxiliary data is valid to convert
    // to a shared reference to callback data of type `C` during the call.
    let callback = unsafe { &*(bindings::debugfs_get_aux((*seq).file).cast::<C>()) };
    // SAFETY: By caller precondition, concurrent accesses to `seq` only read
    // `private`.
    let seq_file = unsafe { SeqFile::from_raw(seq) };
    seq_print!(seq_file, "{}", (CallbackWriter::<D, C> { data, callback }));
    0
}

struct ReadCallbackFile<D>(PhantomData<D>);

impl<D: Sync> ReadCallbackFile<D> {
    const FILE_OPS: FileOps<D, ReadCallback<D>> = {
        let operations = bindings::file_operations {
            read: Some(bindings::seq_read),
            llseek: Some(bindings::seq_lseek),
            release: Some(bindings::single_release),
            open: Some(callback_writer_open::<D, ReadCallback<D>>),
            ..pin_init::zeroed()
        };
        // SAFETY: `callback_writer_act` accesses the inode's `D` pointer and
        // auxiliary `ReadCallback<D>` pointer only from `read` and `llseek`,
        // which debugfs protects against removal. `single_release` accesses neither.
        unsafe { FileOps::new(operations, 0o400) }
    };
}

pub(super) fn read_callback_ops<D>() -> &'static FileOps<D, ReadCallback<D>>
where
    D: Sync + 'static,
{
    &ReadCallbackFile::<D>::FILE_OPS
}

fn read<T: Reader + Sync>(data: &T, buf: *const c_char, count: usize) -> isize {
    let mut reader = UserSlice::new(UserPtr::from_ptr(buf as *mut c_void), count).reader();

    if let Err(e) = data.read_from_slice(&mut reader) {
        return e.to_errno() as isize;
    }

    count as isize
}

/// # Safety
///
/// `file` must be a valid pointer to a `file` struct.
/// The `private_data` of the file must contain a valid pointer to a `seq_file` whose
/// `private` data in turn is valid to convert to a shared reference to a `T` that
/// implements `Reader` during the call.
/// `buf` must be a valid user-space buffer.
pub(crate) unsafe extern "C" fn write<T: Reader + Sync>(
    file: *mut bindings::file,
    buf: *const c_char,
    count: usize,
    _ppos: *mut bindings::loff_t,
) -> isize {
    // SAFETY: By caller precondition, `file` is a valid pointer to a `file`
    // struct, so it is valid to obtain a raw pointer to this field.
    let seq_addr = unsafe { &raw const (*file).private_data };
    // SAFETY: By caller precondition, the `private_data` field points to a
    // live `seq_file`.
    let seq = unsafe { (*seq_addr).cast::<bindings::seq_file>() };
    // SAFETY: By caller precondition, `seq` is live and its `private` field
    // is valid to convert to a shared reference to `T`. `single_open`
    // initializes `private` before file operations run and this file type only
    // reads it, including while the read path may hold a `SeqFile`.
    let data = unsafe { &*((*seq).private.cast::<T>()) };
    read(data, buf, count)
}

// A trait to get the file operations for a type.
pub(crate) trait ReadWriteFile<T> {
    const FILE_OPS: FileOps<T>;
}

impl<T: Writer + Reader + Sync> ReadWriteFile<T> for T {
    const FILE_OPS: FileOps<T> = {
        let operations = bindings::file_operations {
            open: Some(writer_open::<T>),
            read: Some(bindings::seq_read),
            write: Some(write::<T>),
            llseek: Some(bindings::seq_lseek),
            release: Some(bindings::single_release),
            ..pin_init::zeroed()
        };
        // SAFETY: `writer_open` stores the inode's `T` pointer for operations
        // protected by debugfs against removal. `write` only reads the stable
        // `seq_file` private pointer installed by `writer_open`.
        // `single_release` does not access the stored pointer.
        unsafe { FileOps::new(operations, 0o600) }
    };
}

/// Runs a write callback on data stashed in a seq file.
///
/// # Safety
///
/// * `file` must be a valid pointer to a `file` struct whose private data
///   points to a live `seq_file`. Its `private` field must be valid to convert
///   to a shared reference to `D`, and the file type must permit reading that
///   field during the call.
/// * The file's auxiliary data must be valid to convert to a shared reference
///   to `ReadWriteCallbacks<D>`.
/// * `buf` must be a valid user-space buffer.
unsafe extern "C" fn read_write_callback_write<D>(
    file: *mut bindings::file,
    buf: *const c_char,
    count: usize,
    _ppos: *mut bindings::loff_t,
) -> isize
where
    D: Sync,
{
    // SAFETY: By caller precondition, `file` is a valid pointer to a `file`
    // struct, so it is valid to obtain a raw pointer to this field.
    let seq_addr = unsafe { &raw const (*file).private_data };
    // SAFETY: By caller precondition, the `private_data` field points to a
    // live `seq_file`.
    let seq = unsafe { (*seq_addr).cast::<bindings::seq_file>() };
    // SAFETY: By caller precondition, `seq` is live and its `private` field
    // is valid to convert to a shared reference to `D`. `callback_writer_open`
    // initializes `private` before file operations run and this file type only
    // reads it, including while the read path may hold a `SeqFile`.
    let data = unsafe { &*((*seq).private.cast::<D>()) };
    // SAFETY: By caller precondition, the file's auxiliary data is valid to
    // convert to a shared reference to `ReadWriteCallbacks<D>`.
    let callback = unsafe { &*(bindings::debugfs_get_aux(file).cast::<ReadWriteCallbacks<D>>()) };
    let mut reader = UserSlice::new(UserPtr::from_ptr(buf as *mut c_void), count).reader();

    match (callback.write)(data, &mut reader) {
        Ok(()) => count as isize,
        Err(e) => e.to_errno() as isize,
    }
}

struct ReadWriteCallbackFile<D>(PhantomData<D>);

impl<D: Sync> ReadWriteCallbackFile<D> {
    const FILE_OPS: FileOps<D, ReadWriteCallbacks<D>> = {
        let operations = bindings::file_operations {
            open: Some(callback_writer_open::<D, ReadWriteCallbacks<D>>),
            read: Some(bindings::seq_read),
            write: Some(read_write_callback_write::<D>),
            llseek: Some(bindings::seq_lseek),
            release: Some(bindings::single_release),
            ..pin_init::zeroed()
        };
        // SAFETY: `callback_writer_open` stores the inode's `D` pointer in a
        // seq file. `callback_writer_act` and `read_write_callback_write`
        // access that pointer and the auxiliary `ReadWriteCallbacks<D>`
        // pointer only from operations protected by debugfs against removal.
        // `single_release` accesses neither stored pointer.
        unsafe { FileOps::new(operations, 0o600) }
    };
}

pub(super) fn read_write_callback_ops<D>() -> &'static FileOps<D, ReadWriteCallbacks<D>>
where
    D: Sync + 'static,
{
    &ReadWriteCallbackFile::<D>::FILE_OPS
}

/// # Safety
///
/// `inode` must be a valid pointer to an `inode` struct.
/// `file` must be a valid pointer to a `file` struct.
unsafe extern "C" fn write_only_open(
    inode: *mut bindings::inode,
    file: *mut bindings::file,
) -> c_int {
    // SAFETY: The caller ensures that `inode` and `file` are valid pointers.
    unsafe { (*file).private_data = (*inode).i_private };
    0
}

/// # Safety
///
/// * `file` must be a valid pointer to a `file` struct.
/// * The `private_data` of the file must contain a valid pointer to a `T` that implements
///   `Reader`.
/// * `buf` must be a valid user-space buffer.
pub(crate) unsafe extern "C" fn write_only_write<T: Reader + Sync>(
    file: *mut bindings::file,
    buf: *const c_char,
    count: usize,
    _ppos: *mut bindings::loff_t,
) -> isize {
    // SAFETY: The caller ensures that `file` is a valid pointer and that `private_data` holds a
    // valid pointer to `T`.
    let data = unsafe { &*((*file).private_data as *const T) };
    read(data, buf, count)
}

pub(crate) trait WriteFile<T> {
    const FILE_OPS: FileOps<T>;
}

impl<T: Reader + Sync> WriteFile<T> for T {
    const FILE_OPS: FileOps<T> = {
        let operations = bindings::file_operations {
            open: Some(write_only_open),
            write: Some(write_only_write::<T>),
            llseek: Some(bindings::noop_llseek),
            ..pin_init::zeroed()
        };
        // SAFETY: `write_only_open` stores the inode's `T` pointer for
        // `write_only_write`, which accesses it only from `write`; debugfs
        // protects that operation against removal.
        unsafe { FileOps::new(operations, 0o200) }
    };
}

/// Runs a write callback on data stored in the file private pointer.
///
/// # Safety
///
/// * `file` must be a valid pointer to a `file` struct whose private data is
///   valid to convert to a shared reference to `D`.
/// * The file's auxiliary data must be valid to convert to a shared reference
///   to `WriteCallback<D>`.
/// * `buf` must be a valid user-space buffer.
unsafe extern "C" fn write_callback_write<D>(
    file: *mut bindings::file,
    buf: *const c_char,
    count: usize,
    _ppos: *mut bindings::loff_t,
) -> isize
where
    D: Sync,
{
    // SAFETY: By caller precondition, the file's private data is valid to
    // convert to a shared reference to `D`.
    let data = unsafe { &*((*file).private_data as *const D) };
    // SAFETY: By caller precondition, the file's auxiliary data is valid to
    // convert to a shared reference to `WriteCallback<D>`.
    let callback = unsafe { &*(bindings::debugfs_get_aux(file).cast::<WriteCallback<D>>()) };
    let mut reader = UserSlice::new(UserPtr::from_ptr(buf as *mut c_void), count).reader();

    match callback(data, &mut reader) {
        Ok(()) => count as isize,
        Err(e) => e.to_errno() as isize,
    }
}

struct WriteCallbackFile<D>(PhantomData<D>);

impl<D: Sync> WriteCallbackFile<D> {
    const FILE_OPS: FileOps<D, WriteCallback<D>> = {
        let operations = bindings::file_operations {
            open: Some(write_only_open),
            write: Some(write_callback_write::<D>),
            llseek: Some(bindings::noop_llseek),
            ..pin_init::zeroed()
        };
        // SAFETY: `write_only_open` stores the inode's `D` pointer in the
        // file private pointer. `write_callback_write` accesses it and the
        // auxiliary `WriteCallback<D>` pointer only from `write`, which
        // debugfs protects against removal.
        unsafe { FileOps::new(operations, 0o200) }
    };
}

pub(super) fn write_callback_ops<D>() -> &'static FileOps<D, WriteCallback<D>>
where
    D: Sync + 'static,
{
    &WriteCallbackFile::<D>::FILE_OPS
}

extern "C" fn blob_read<T: BinaryWriter>(
    file: *mut bindings::file,
    buf: *mut c_char,
    count: usize,
    ppos: *mut bindings::loff_t,
) -> isize {
    // SAFETY:
    // - `file` is a valid pointer to a `struct file`.
    // - This callback is installed only for files whose private data was
    //   registered from a shared reference to a `T` that remains live while
    //   the callback runs.
    let this = unsafe { &*((*file).private_data.cast::<T>()) };

    // SAFETY:
    // - `ppos` is a valid `file::Offset` pointer.
    // - We have exclusive access to `ppos`.
    let pos: &mut file::Offset = unsafe { &mut *ppos };

    let mut writer = UserSlice::new(UserPtr::from_ptr(buf.cast()), count).writer();

    let ret = || -> Result<isize> {
        let written = this.write_to_slice(&mut writer, pos)?;

        Ok(written.try_into()?)
    }();

    match ret {
        Ok(n) => n,
        Err(e) => e.to_errno() as isize,
    }
}

/// Representation of [`FileOps`] for read only binary files.
pub(crate) trait BinaryReadFile<T> {
    const FILE_OPS: FileOps<T>;
}

impl<T: BinaryWriter + Sync> BinaryReadFile<T> for T {
    const FILE_OPS: FileOps<T> = {
        let operations = bindings::file_operations {
            read: Some(blob_read::<T>),
            llseek: Some(bindings::default_llseek),
            open: Some(bindings::simple_open),
            ..pin_init::zeroed()
        };

        // SAFETY:
        // - Debugfs protects accesses to the inode private pointer, which
        //   points to a valid `T`, against removal.
        // - `simple_open()` stores the `struct inode`'s private data in the private data of the
        //   corresponding `struct file`.
        // - `blob_read()` re-creates a reference to `T` from the `struct file`'s private data.
        // - `default_llseek()` does not access the `struct file`'s private data.
        unsafe { FileOps::new(operations, 0o400) }
    };
}

extern "C" fn blob_write<T: BinaryReader>(
    file: *mut bindings::file,
    buf: *const c_char,
    count: usize,
    ppos: *mut bindings::loff_t,
) -> isize {
    // SAFETY:
    // - `file` is a valid pointer to a `struct file`.
    // - This callback is installed only for files whose private data was
    //   registered from a shared reference to a `T` that remains live while
    //   the callback runs.
    let this = unsafe { &*((*file).private_data.cast::<T>()) };

    // SAFETY:
    // - `ppos` is a valid `file::Offset` pointer.
    // - We have exclusive access to `ppos`.
    let pos: &mut file::Offset = unsafe { &mut *ppos };

    let mut reader = UserSlice::new(UserPtr::from_ptr(buf.cast_mut().cast()), count).reader();

    let ret = || -> Result<isize> {
        let read = this.read_from_slice(&mut reader, pos)?;

        Ok(read.try_into()?)
    }();

    match ret {
        Ok(n) => n,
        Err(e) => e.to_errno() as isize,
    }
}

/// Representation of [`FileOps`] for write only binary files.
pub(crate) trait BinaryWriteFile<T> {
    const FILE_OPS: FileOps<T>;
}

impl<T: BinaryReader + Sync> BinaryWriteFile<T> for T {
    const FILE_OPS: FileOps<T> = {
        let operations = bindings::file_operations {
            write: Some(blob_write::<T>),
            llseek: Some(bindings::default_llseek),
            open: Some(bindings::simple_open),
            ..pin_init::zeroed()
        };

        // SAFETY:
        // - Debugfs protects accesses to the inode private pointer, which
        //   points to a valid `T`, against removal.
        // - `simple_open()` stores the `struct inode`'s private data in the private data of the
        //   corresponding `struct file`.
        // - `blob_write()` re-creates a reference to `T` from the `struct file`'s private data.
        // - `default_llseek()` does not access the `struct file`'s private data.
        unsafe { FileOps::new(operations, 0o200) }
    };
}

/// Representation of [`FileOps`] for read/write binary files.
pub(crate) trait BinaryReadWriteFile<T> {
    const FILE_OPS: FileOps<T>;
}

impl<T: BinaryWriter + BinaryReader + Sync> BinaryReadWriteFile<T> for T {
    const FILE_OPS: FileOps<T> = {
        let operations = bindings::file_operations {
            read: Some(blob_read::<T>),
            write: Some(blob_write::<T>),
            llseek: Some(bindings::default_llseek),
            open: Some(bindings::simple_open),
            ..pin_init::zeroed()
        };

        // SAFETY:
        // - Debugfs protects accesses to the inode private pointer, which
        //   points to a valid `T`, against removal.
        // - `simple_open()` stores the `struct inode`'s private data in the private data of the
        //   corresponding `struct file`.
        // - `blob_read()` re-creates a reference to `T` from the `struct file`'s private data.
        // - `blob_write()` re-creates a reference to `T` from the `struct file`'s private data.
        // - `default_llseek()` does not access the `struct file`'s private data.
        unsafe { FileOps::new(operations, 0o600) }
    };
}
