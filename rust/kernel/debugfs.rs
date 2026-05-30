// SPDX-License-Identifier: GPL-2.0
// Copyright (C) 2025 Google LLC.

//! DebugFS Abstraction
//!
//! C header: [`include/linux/debugfs.h`](srctree/include/linux/debugfs.h)

// When DebugFS is disabled, many parameters are dead. Linting for this isn't helpful.
#![cfg_attr(not(CONFIG_DEBUG_FS), allow(unused_variables))]

#[cfg(CONFIG_DEBUG_FS)]
use crate::sync::Arc;
use crate::{
    fmt,
    prelude::*,
    str::CStr,
    uaccess::UserSliceReader, //
};

#[cfg(CONFIG_DEBUG_FS)]
use core::mem::ManuallyDrop;
use core::{
    marker::{
        PhantomData,
        PhantomPinned, //
    },
    ops::Deref,
};

mod traits;
pub use traits::{
    BinaryReader,
    BinaryReaderMut,
    BinaryWriter,
    Reader,
    Writer, //
};

/// Callback retained by a read-only callback file.
pub type ReadCallback<T> = fn(&T, &mut fmt::Formatter<'_>) -> fmt::Result;

/// Callback retained by a write-only callback file.
pub type WriteCallback<T> = fn(&T, &mut UserSliceReader) -> Result;

/// Callbacks retained by a read-write callback file.
pub struct ReadWriteCallbacks<T> {
    read: fn(&T, &mut fmt::Formatter<'_>) -> fmt::Result,
    write: fn(&T, &mut UserSliceReader) -> Result,
}

impl<T> ReadWriteCallbacks<T> {
    /// Creates callback state for a read-write callback file.
    #[inline]
    pub const fn new(
        read: fn(&T, &mut fmt::Formatter<'_>) -> fmt::Result,
        write: fn(&T, &mut UserSliceReader) -> Result,
    ) -> Self {
        Self { read, write }
    }
}

mod file_ops;
use file_ops::{
    read_callback_ops,
    read_write_callback_ops,
    write_callback_ops,
    BinaryReadFile,
    BinaryReadWriteFile,
    BinaryWriteFile,
    FileOps,
    ReadFile,
    ReadWriteFile,
    WriteFile, //
};

#[cfg(CONFIG_DEBUG_FS)]
mod entry;
#[cfg(CONFIG_DEBUG_FS)]
use entry::Entry;

/// Owning handle to a DebugFS directory.
///
/// The directory in the filesystem represented by [`Dir`] will be removed when handle has been
/// dropped *and* all children have been removed.
// If we have a parent, we hold a reference to it in the `Entry`. This prevents the `dentry`
// we point to from being cleaned up if our parent `Dir`/`Entry` is dropped before us.
//
// The `None` option indicates that the `Arc` could not be allocated, so our children would not be
// able to refer to us. In this case, we need to silently fail. All future child directories/files
// will silently fail as well.
#[derive(Clone)]
pub struct Dir(#[cfg(CONFIG_DEBUG_FS)] Option<Arc<Entry<'static>>>);

impl Dir {
    /// Create a new directory in DebugFS. If `parent` is [`None`], it will be created at the root.
    fn create(name: &CStr, parent: Option<&Dir>) -> Self {
        #[cfg(CONFIG_DEBUG_FS)]
        {
            let parent_entry = match parent {
                // If the parent couldn't be allocated, just early-return
                Some(Dir(None)) => return Self(None),
                Some(Dir(Some(entry))) => Some(entry.clone()),
                None => None,
            };
            Self(
                // If Arc creation fails, the `Entry` will be dropped, so the directory will be
                // cleaned up.
                Arc::new(Entry::dynamic_dir(name, parent_entry), GFP_KERNEL).ok(),
            )
        }
        #[cfg(not(CONFIG_DEBUG_FS))]
        Self()
    }

    /// Creates a DebugFS file which will own the data produced by the initializer provided in
    /// `data`.
    fn create_file<'a, T, A, E: 'a>(
        &'a self,
        name: &'a CStr,
        data: impl PinInit<T, E> + 'a,
        aux: &'static A,
        file_ops: &'static FileOps<T, A>,
    ) -> impl PinInit<File<T>, E> + 'a
    where
        T: Sync + 'static,
    {
        let scope = Scope::<T>::new(data, move |data| {
            #[cfg(CONFIG_DEBUG_FS)]
            if let Some(parent) = &self.0 {
                Entry::dynamic_file(name, parent.clone(), data.data, aux, file_ops)
            } else {
                Entry::empty()
            }
        });
        try_pin_init! {
            File {
                scope <- scope
            } ? E
        }
    }

    /// Create a new directory in DebugFS at the root.
    ///
    /// # Examples
    ///
    /// ```
    /// # use kernel::debugfs::Dir;
    /// let debugfs = Dir::new(c"parent");
    /// ```
    pub fn new(name: &CStr) -> Self {
        Dir::create(name, None)
    }

    /// Creates a subdirectory within this directory.
    ///
    /// # Examples
    ///
    /// ```
    /// # use kernel::debugfs::Dir;
    /// let parent = Dir::new(c"parent");
    /// let child = parent.subdir(c"child");
    /// ```
    pub fn subdir(&self, name: &CStr) -> Self {
        Dir::create(name, Some(self))
    }

    /// Creates a read-only file in this directory.
    ///
    /// The file's contents are produced by invoking [`Writer::write`] on the value initialized by
    /// `data`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use kernel::debugfs::Dir;
    /// # use kernel::prelude::*;
    /// # let dir = Dir::new(c"my_debugfs_dir");
    /// let file = KBox::pin_init(dir.read_only_file(c"foo", 200), GFP_KERNEL)?;
    /// // "my_debugfs_dir/foo" now contains the number 200.
    /// // The file is removed when `file` is dropped.
    /// # Ok::<(), Error>(())
    /// ```
    pub fn read_only_file<'a, T, E: 'a>(
        &'a self,
        name: &'a CStr,
        data: impl PinInit<T, E> + 'a,
    ) -> impl PinInit<File<T>, E> + 'a
    where
        T: Writer + Send + Sync + 'static,
    {
        let file_ops = &<T as ReadFile<_>>::FILE_OPS;
        self.create_file(name, data, &(), file_ops)
    }

    /// Creates a read-only binary file in this directory.
    ///
    /// The file's contents are produced by invoking [`BinaryWriter::write_to_slice`] on the value
    /// initialized by `data`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use kernel::debugfs::Dir;
    /// # use kernel::prelude::*;
    /// # let dir = Dir::new(c"my_debugfs_dir");
    /// let file = KBox::pin_init(dir.read_binary_file(c"foo", [0x1, 0x2]), GFP_KERNEL)?;
    /// # Ok::<(), Error>(())
    /// ```
    pub fn read_binary_file<'a, T, E: 'a>(
        &'a self,
        name: &'a CStr,
        data: impl PinInit<T, E> + 'a,
    ) -> impl PinInit<File<T>, E> + 'a
    where
        T: BinaryWriter + Send + Sync + 'static,
    {
        self.create_file(name, data, &(), &T::FILE_OPS)
    }

    /// Creates a read-only file in this directory, with contents from a callback.
    ///
    /// `callback` is retained for the lifetime of the file and must have static storage.
    ///
    /// # Examples
    ///
    /// ```
    /// # use kernel::{
    /// #     debugfs::{
    /// #         Dir,
    /// #         ReadCallback,
    /// #     },
    /// #     prelude::*,
    /// #     sync::atomic::{
    /// #         Atomic,
    /// #         Relaxed,
    /// #     },
    /// # };
    /// # let dir = Dir::new(c"foo");
    /// static READ: ReadCallback<Atomic<u32>> = |val, f| {
    ///     let out = val.load(Relaxed);
    ///     writeln!(f, "{out:#010x}")
    /// };
    /// let file = KBox::pin_init(
    ///     dir.read_callback_file(c"bar",
    ///     Atomic::<u32>::new(3),
    ///     &READ),
    ///     GFP_KERNEL)?;
    /// // Reading "foo/bar" will show "0x00000003".
    /// file.store(10, Relaxed);
    /// // Reading "foo/bar" will now show "0x0000000a".
    /// # Ok::<(), Error>(())
    /// ```
    pub fn read_callback_file<'a, T, E: 'a>(
        &'a self,
        name: &'a CStr,
        data: impl PinInit<T, E> + 'a,
        callback: &'static ReadCallback<T>,
    ) -> impl PinInit<File<T>, E> + 'a
    where
        T: Send + Sync + 'static,
    {
        let file_ops = read_callback_ops::<T>();
        self.create_file(name, data, callback, file_ops)
    }

    /// Creates a read-write file in this directory.
    ///
    /// Reading the file uses the [`Writer`] implementation.
    /// Writing to the file uses the [`Reader`] implementation.
    pub fn read_write_file<'a, T, E: 'a>(
        &'a self,
        name: &'a CStr,
        data: impl PinInit<T, E> + 'a,
    ) -> impl PinInit<File<T>, E> + 'a
    where
        T: Writer + Reader + Send + Sync + 'static,
    {
        let file_ops = &<T as ReadWriteFile<_>>::FILE_OPS;
        self.create_file(name, data, &(), file_ops)
    }

    /// Creates a read-write binary file in this directory.
    ///
    /// Reading the file uses the [`BinaryWriter`] implementation.
    /// Writing to the file uses the [`BinaryReader`] implementation.
    pub fn read_write_binary_file<'a, T, E: 'a>(
        &'a self,
        name: &'a CStr,
        data: impl PinInit<T, E> + 'a,
    ) -> impl PinInit<File<T>, E> + 'a
    where
        T: BinaryWriter + BinaryReader + Send + Sync + 'static,
    {
        let file_ops = &<T as BinaryReadWriteFile<_>>::FILE_OPS;
        self.create_file(name, data, &(), file_ops)
    }

    /// Creates a read-write file in this directory, with logic from callbacks.
    ///
    /// Reading from and writing to the file are handled by `callbacks`.
    /// `callbacks` is retained for the lifetime of the file and must have static storage.
    ///
    /// # Examples
    ///
    /// ```
    /// # use kernel::{
    /// #     debugfs::{Dir, ReadWriteCallbacks},
    /// #     prelude::*,
    /// # };
    /// # let dir = Dir::new(c"foo");
    /// static CALLBACKS: ReadWriteCallbacks<u32> = ReadWriteCallbacks::new(
    ///     |value, f| writeln!(f, "{value}"),
    ///     |_, _| Ok(()),
    /// );
    /// let _file = KBox::pin_init(
    ///     dir.read_write_callback_file(c"bar", 3, &CALLBACKS),
    ///     GFP_KERNEL)?;
    /// # Ok::<(), Error>(())
    /// ```
    pub fn read_write_callback_file<'a, T, E: 'a>(
        &'a self,
        name: &'a CStr,
        data: impl PinInit<T, E> + 'a,
        callbacks: &'static ReadWriteCallbacks<T>,
    ) -> impl PinInit<File<T>, E> + 'a
    where
        T: Send + Sync + 'static,
    {
        let file_ops = read_write_callback_ops::<T>();
        self.create_file(name, data, callbacks, file_ops)
    }

    /// Creates a write-only file in this directory.
    ///
    /// The file owns its backing data. Writing to the file uses the [`Reader`]
    /// implementation.
    ///
    /// The file is removed when the returned [`File`] is dropped.
    pub fn write_only_file<'a, T, E: 'a>(
        &'a self,
        name: &'a CStr,
        data: impl PinInit<T, E> + 'a,
    ) -> impl PinInit<File<T>, E> + 'a
    where
        T: Reader + Send + Sync + 'static,
    {
        self.create_file(name, data, &(), &T::FILE_OPS)
    }

    /// Creates a write-only binary file in this directory.
    ///
    /// The file owns its backing data. Writing to the file uses the [`BinaryReader`]
    /// implementation.
    ///
    /// The file is removed when the returned [`File`] is dropped.
    pub fn write_binary_file<'a, T, E: 'a>(
        &'a self,
        name: &'a CStr,
        data: impl PinInit<T, E> + 'a,
    ) -> impl PinInit<File<T>, E> + 'a
    where
        T: BinaryReader + Send + Sync + 'static,
    {
        self.create_file(name, data, &(), &T::FILE_OPS)
    }

    /// Creates a write-only file in this directory, with write logic from a callback.
    ///
    /// `callback` is retained for the lifetime of the file and must have static storage.
    pub fn write_callback_file<'a, T, E: 'a>(
        &'a self,
        name: &'a CStr,
        data: impl PinInit<T, E> + 'a,
        callback: &'static WriteCallback<T>,
    ) -> impl PinInit<File<T>, E> + 'a
    where
        T: Send + Sync + 'static,
    {
        let file_ops = write_callback_ops::<T>();
        self.create_file(name, data, callback, file_ops)
    }

    // While this function is safe, it is intentionally not public because it's a bit of a
    // footgun.
    //
    // Unless you also extract the `entry` later and schedule it for `Drop` at the appropriate
    // time, a `ScopedDir` with a `Dir` parent will never be deleted.
    fn scoped_dir<'data>(&self, name: &CStr) -> ScopedDir<'data, 'static> {
        #[cfg(CONFIG_DEBUG_FS)]
        {
            let parent_entry = match &self.0 {
                None => return ScopedDir::empty(),
                Some(entry) => entry.clone(),
            };
            ScopedDir {
                entry: ManuallyDrop::new(Entry::dynamic_dir(name, Some(parent_entry))),
                _phantom: PhantomData,
            }
        }
        #[cfg(not(CONFIG_DEBUG_FS))]
        ScopedDir::empty()
    }

    /// Creates a new scope, which is a directory associated with some data `T`.
    ///
    /// The created directory will be a subdirectory of `self`. The `init` closure is called to
    /// populate the directory with files and subdirectories. These files can reference the data
    /// stored in the scope.
    ///
    /// The entire directory tree created within the scope will be removed when the returned
    /// `Scope` handle is dropped.
    pub fn scope<'a, T: 'a, E: 'a, F>(
        &'a self,
        data: impl PinInit<T, E> + 'a,
        name: &'a CStr,
        init: F,
    ) -> impl PinInit<Scope<T>, E> + 'a
    where
        F: for<'data, 'dir> FnOnce(ScopedRef<'data, T>, &'dir ScopedDir<'data, 'dir>) + 'a,
    {
        Scope::new(data, |data| {
            let scoped = self.scoped_dir(name);
            init(data, &scoped);
            scoped.into_entry()
        })
    }
}

#[pin_data]
/// Handle to a DebugFS scope, which ensures that attached `data` will outlive the DebugFS entry
/// without moving.
///
/// This is internally used to back [`File`], and used in the API to represent the attachment
/// of a directory lifetime to a data structure which may be jointly accessed by a number of
/// different files.
///
/// When dropped, a `Scope` will remove all directories and files in the filesystem backed by the
/// attached data structure prior to releasing the attached data.
/// The full debugfs proxy holds an active-user reference while operations access the attached
/// data, so removing the entry waits for them to complete before releasing it.
pub struct Scope<T> {
    // This order is load-bearing for drops - `_entry` must be dropped before `data`.
    #[cfg(CONFIG_DEBUG_FS)]
    _entry: Entry<'static>,
    #[pin]
    data: T,
    // Even if `T` is `Unpin`, we still can't allow it to be moved.
    #[pin]
    _pin: PhantomPinned,
}

#[pin_data]
/// Handle to a DebugFS file, owning its backing data.
///
/// When dropped, the DebugFS file will be removed and the attached data will be dropped.
pub struct File<T> {
    #[pin]
    scope: Scope<T>,
}

#[cfg(not(CONFIG_DEBUG_FS))]
impl<'b, T: 'b> Scope<T> {
    fn new<E: 'b, F>(data: impl PinInit<T, E> + 'b, init: F) -> impl PinInit<Self, E> + 'b
    where
        F: for<'a> FnOnce(ScopedRef<'a, T>) + 'b,
    {
        try_pin_init! {
            Self {
                data <- data,
                _pin: PhantomPinned
            } ? E
        }
        .pin_chain(|scope| {
            init(ScopedRef::new(&scope.data));
            Ok(())
        })
    }
}

#[cfg(CONFIG_DEBUG_FS)]
impl<'b, T: 'b> Scope<T> {
    fn entry_mut(self: Pin<&mut Self>) -> &mut Entry<'static> {
        // SAFETY: _entry is not structurally pinned.
        unsafe { &mut Pin::into_inner_unchecked(self)._entry }
    }

    fn new<E: 'b, F>(data: impl PinInit<T, E> + 'b, init: F) -> impl PinInit<Self, E> + 'b
    where
        F: for<'a> FnOnce(ScopedRef<'a, T>) -> Entry<'a> + 'b,
    {
        try_pin_init! {
            Self {
                _entry: Entry::empty(),
                data <- data,
                _pin: PhantomPinned
            } ? E
        }
        .pin_chain(|scope| {
            let entry = init(ScopedRef::new(&scope.data));
            // SAFETY: `init` may create an entry or entry tree pointing into
            // `data`. `scope` is pinned, so `data` cannot move. The field
            // order ensures that `_entry` removes that tree before `data` is
            // dropped. The full debugfs proxy holds an active-user reference
            // while invoking operations that access pointers into `data`, so
            // removal waits for them; `release` does not access those pointers.
            let entry = unsafe { core::mem::transmute::<Entry<'_>, Entry<'static>>(entry) };
            *scope.entry_mut() = entry;
            Ok(())
        })
    }
}

impl<'a, T: 'a> Scope<T> {
    /// Creates a new scope, which is a directory at the root of the debugfs filesystem,
    /// associated with some data `T`.
    ///
    /// The `init` closure is called to populate the directory with files and subdirectories. These
    /// files can reference the data stored in the scope.
    ///
    /// The entire directory tree created within the scope will be removed when the returned
    /// `Scope` handle is dropped.
    pub fn dir<E: 'a, F>(
        data: impl PinInit<T, E> + 'a,
        name: &'a CStr,
        init: F,
    ) -> impl PinInit<Self, E> + 'a
    where
        F: for<'data, 'dir> FnOnce(ScopedRef<'data, T>, &'dir ScopedDir<'data, 'dir>) + 'a,
    {
        Scope::new(data, |data| {
            let scoped = ScopedDir::new(name);
            init(data, &scoped);
            scoped.into_entry()
        })
    }
}

impl<T> Deref for Scope<T> {
    type Target = T;
    fn deref(&self) -> &T {
        &self.data
    }
}

impl<T> Deref for File<T> {
    type Target = T;
    fn deref(&self) -> &T {
        &self.scope
    }
}

/// A witness for a value whose address remains valid while a [`Scope`] may use it.
///
/// A scope can outlive forgotten owning handles, so scoped file registration
/// accepts this type instead of arbitrary references. Use [`project!`] for
/// structural projections into scope-owned storage.
pub struct ScopedRef<'data, T: ?Sized> {
    data: &'data T,
}

impl<'data, T: ?Sized> ScopedRef<'data, T> {
    fn new(data: &'data T) -> Self {
        Self { data }
    }

    /// Creates a witness for data with static storage.
    #[inline]
    pub fn from_static(data: &'static T) -> Self {
        Self { data }
    }

    /// Projects through owned or static storage reachable from a `'static` value.
    ///
    /// The source value and any captured state contain no non-static
    /// borrows, so a returned borrow remains live if the scope is forgotten.
    #[inline]
    pub fn project_static<U: ?Sized, F>(self, project: F) -> ScopedRef<'data, U>
    where
        T: 'static,
        F: for<'a> FnOnce(&'a T) -> &'a U + 'static,
    {
        ScopedRef::new(project(self.data))
    }

    #[doc(hidden)]
    #[inline]
    pub fn __as_ptr(self) -> *const T {
        core::ptr::from_ref(self.data)
    }

    /// # Safety
    ///
    /// `ptr` must point within the storage of the value represented by
    /// `self`.
    #[doc(hidden)]
    #[inline]
    pub unsafe fn __from_projected_ptr<U: ?Sized>(self, ptr: *const U) -> ScopedRef<'data, U> {
        // SAFETY: By caller precondition, `ptr` points within `self.data`.
        ScopedRef::new(unsafe { &*ptr })
    }
}

impl<T: ?Sized> Clone for ScopedRef<'_, T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T: ?Sized> Copy for ScopedRef<'_, T> {}

impl<T: ?Sized> Deref for ScopedRef<'_, T> {
    type Target = T;

    fn deref(&self) -> &T {
        self.data
    }
}

/// Projects a [`ScopedRef`] into inline scope-owned storage.
///
/// Projection syntax is the same as [`crate::ptr::project!`]. In particular,
/// it does not project through types implementing [`Deref`] or [`Index`],
/// since those may reach storage outside the scoped value.
///
/// [`Index`]: core::ops::Index
#[macro_export]
macro_rules! debugfs_project {
    ($data:expr, $($proj:tt)*) => {{
        let data = $data;
        let ptr = $crate::ptr::project!(data.__as_ptr(), $($proj)*);
        // SAFETY: `ptr::project!` returns a pointer within the storage
        // represented by `data`.
        unsafe { data.__from_projected_ptr(ptr) }
    }};
}

pub use crate::debugfs_project as project;

/// A handle to a directory which will live at most `'dir`, accessing data that will live for at
/// least `'data`.
///
/// Dropping a ScopedDir will not delete or clean it up, this is expected to occur through dropping
/// the `Scope` that created it.
pub struct ScopedDir<'data, 'dir> {
    #[cfg(CONFIG_DEBUG_FS)]
    entry: ManuallyDrop<Entry<'dir>>,
    _phantom: PhantomData<fn(&'data ()) -> &'dir ()>,
}

impl<'data, 'dir> ScopedDir<'data, 'dir> {
    /// Creates a subdirectory inside this `ScopedDir`.
    ///
    /// The returned directory handle cannot outlive this one.
    pub fn dir<'dir2>(&'dir2 self, name: &CStr) -> ScopedDir<'data, 'dir2> {
        #[cfg(not(CONFIG_DEBUG_FS))]
        let _ = name;
        ScopedDir {
            #[cfg(CONFIG_DEBUG_FS)]
            entry: ManuallyDrop::new(Entry::dir(name, Some(&*self.entry))),
            _phantom: PhantomData,
        }
    }

    fn create_file<T: Sync, A>(
        &self,
        name: &CStr,
        data: ScopedRef<'data, T>,
        aux: ScopedRef<'data, A>,
        vtable: &'static FileOps<T, A>,
    ) {
        #[cfg(CONFIG_DEBUG_FS)]
        core::mem::forget(Entry::file(name, &self.entry, data.data, aux.data, vtable));
    }

    /// Creates a read-only file in this directory.
    ///
    /// The file's contents are produced by invoking [`Writer::write`].
    ///
    /// This function does not produce an owning handle to the file. The created
    /// file is removed when the [`Scope`] that this directory belongs
    /// to is dropped.
    pub fn read_only_file<T: Writer + Send + Sync + 'static>(
        &self,
        name: &CStr,
        data: ScopedRef<'data, T>,
    ) {
        self.create_file(name, data, ScopedRef::new(&()), &T::FILE_OPS)
    }

    /// Creates a read-only binary file in this directory.
    ///
    /// The file's contents are produced by invoking [`BinaryWriter::write_to_slice`].
    ///
    /// This function does not produce an owning handle to the file. The created file is removed
    /// when the [`Scope`] that this directory belongs to is dropped.
    pub fn read_binary_file<T: BinaryWriter + Send + Sync + 'static>(
        &self,
        name: &CStr,
        data: ScopedRef<'data, T>,
    ) {
        self.create_file(name, data, ScopedRef::new(&()), &T::FILE_OPS)
    }

    /// Creates a read-only file in this directory, with contents from a callback.
    ///
    /// The file contents are generated by calling `callback` with `data`.
    /// `callback` is retained until the surrounding [`Scope`] removes the file,
    /// so it may be stored in `data`.
    ///
    /// This function does not produce an owning handle to the file. The created
    /// file is removed when the [`Scope`] that this directory belongs
    /// to is dropped.
    pub fn read_callback_file<T>(
        &self,
        name: &CStr,
        data: ScopedRef<'data, T>,
        callback: ScopedRef<'data, ReadCallback<T>>,
    ) where
        T: Send + Sync + 'static,
    {
        let vtable = read_callback_ops::<T>();
        self.create_file(name, data, callback, vtable)
    }

    /// Creates a read-write file in this directory.
    ///
    /// Reading the file uses the [`Writer`] implementation on `data`. Writing to the file uses
    /// the [`Reader`] implementation on `data`.
    ///
    /// This function does not produce an owning handle to the file. The created
    /// file is removed when the [`Scope`] that this directory belongs
    /// to is dropped.
    pub fn read_write_file<T: Writer + Reader + Send + Sync + 'static>(
        &self,
        name: &CStr,
        data: ScopedRef<'data, T>,
    ) {
        let vtable = &<T as ReadWriteFile<_>>::FILE_OPS;
        self.create_file(name, data, ScopedRef::new(&()), vtable)
    }

    /// Creates a read-write binary file in this directory.
    ///
    /// Reading the file uses the [`BinaryWriter`] implementation on `data`. Writing to the file
    /// uses the [`BinaryReader`] implementation on `data`.
    ///
    /// This function does not produce an owning handle to the file. The created file is removed
    /// when the [`Scope`] that this directory belongs to is dropped.
    pub fn read_write_binary_file<T: BinaryWriter + BinaryReader + Send + Sync + 'static>(
        &self,
        name: &CStr,
        data: ScopedRef<'data, T>,
    ) {
        let vtable = &<T as BinaryReadWriteFile<_>>::FILE_OPS;
        self.create_file(name, data, ScopedRef::new(&()), vtable)
    }

    /// Creates a read-write file in this directory, with logic from callbacks.
    ///
    /// Reading from and writing to the file are handled by `callbacks`.
    /// `callbacks` is retained until the surrounding [`Scope`] removes the file,
    /// so it may be stored in `data`.
    ///
    /// This function does not produce an owning handle to the file. The created
    /// file is removed when the [`Scope`] that this directory belongs
    /// to is dropped.
    pub fn read_write_callback_file<T>(
        &self,
        name: &CStr,
        data: ScopedRef<'data, T>,
        callbacks: ScopedRef<'data, ReadWriteCallbacks<T>>,
    ) where
        T: Send + Sync + 'static,
    {
        let vtable = read_write_callback_ops::<T>();
        self.create_file(name, data, callbacks, vtable)
    }

    /// Creates a write-only file in this directory.
    ///
    /// Writing to the file uses the [`Reader`] implementation on `data`.
    ///
    /// This function does not produce an owning handle to the file. The created
    /// file is removed when the [`Scope`] that this directory belongs
    /// to is dropped.
    pub fn write_only_file<T: Reader + Send + Sync + 'static>(
        &self,
        name: &CStr,
        data: ScopedRef<'data, T>,
    ) {
        let vtable = &<T as WriteFile<_>>::FILE_OPS;
        self.create_file(name, data, ScopedRef::new(&()), vtable)
    }

    /// Creates a write-only binary file in this directory.
    ///
    /// Writing to the file uses the [`BinaryReader`] implementation on `data`.
    ///
    /// This function does not produce an owning handle to the file. The created file is removed
    /// when the [`Scope`] that this directory belongs to is dropped.
    pub fn write_binary_file<T: BinaryReader + Send + Sync + 'static>(
        &self,
        name: &CStr,
        data: ScopedRef<'data, T>,
    ) {
        self.create_file(name, data, ScopedRef::new(&()), &T::FILE_OPS)
    }

    /// Creates a write-only file in this directory, with write logic from a callback.
    ///
    /// Writing to the file is handled by `callback`.
    /// `callback` is retained until the surrounding [`Scope`] removes the file,
    /// so it may be stored in `data`.
    ///
    /// This function does not produce an owning handle to the file. The created
    /// file is removed when the [`Scope`] that this directory belongs
    /// to is dropped.
    pub fn write_only_callback_file<T>(
        &self,
        name: &CStr,
        data: ScopedRef<'data, T>,
        callback: ScopedRef<'data, WriteCallback<T>>,
    ) where
        T: Send + Sync + 'static,
    {
        let vtable = write_callback_ops::<T>();
        self.create_file(name, data, callback, vtable)
    }

    fn empty() -> Self {
        ScopedDir {
            #[cfg(CONFIG_DEBUG_FS)]
            entry: ManuallyDrop::new(Entry::empty()),
            _phantom: PhantomData,
        }
    }
    #[cfg(CONFIG_DEBUG_FS)]
    fn into_entry(self) -> Entry<'dir> {
        ManuallyDrop::into_inner(self.entry)
    }
    #[cfg(not(CONFIG_DEBUG_FS))]
    fn into_entry(self) {}
}

impl<'data> ScopedDir<'data, 'static> {
    // This is safe, but intentionally not exported due to footgun status. A ScopedDir with no
    // parent will never be released by default, and needs to have its entry extracted and used
    // somewhere.
    fn new(name: &CStr) -> ScopedDir<'data, 'static> {
        ScopedDir {
            #[cfg(CONFIG_DEBUG_FS)]
            entry: ManuallyDrop::new(Entry::dir(name, None)),
            _phantom: PhantomData,
        }
    }
}
