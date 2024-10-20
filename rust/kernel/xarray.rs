// SPDX-License-Identifier: GPL-2.0

//! XArray abstraction.
//!
//! C header: [`include/linux/xarray.h`](srctree/include/linux/xarray.h)

use core::pin::Pin;

use crate::{
    alloc, bindings, build_assert, build_error,
    error::Error,
    init::PinInit,
    pin_init,
    types::{ForeignOwnable, Opaque},
};
use core::{ffi::c_ulong, iter, marker::PhantomData, mem, ops};
use macros::{pin_data, pinned_drop};

/// An array which efficiently maps sparse integer indices to owned objects.
///
/// This is similar to a [`crate::alloc::kvec::Vec<Option<T>>`], but more efficient when there are
/// holes in the index space, and can be efficiently grown.
///
/// # Invariants
///
/// `self.xa` is always an initialized and valid [`XArray`].
///
/// # Examples
///
/// ```rust
/// use kernel::alloc::KBox;
/// use kernel::xarray::{AllocKind, XArray};
///
/// let foo = KBox::new("foo", GFP_KERNEL)?;
/// let bar = KBox::new("bar", GFP_KERNEL)?;
/// let baz = KBox::new("baz", GFP_KERNEL)?;
///
/// let xa = KBox::pin_init(XArray::new(AllocKind::Alloc1), GFP_KERNEL)?;
///
/// let mut guard = xa.lock();
///
/// let index = guard.insert_limit(.., foo, GFP_KERNEL).unwrap();
/// assert_eq!(index, 1); // AllocKind::Alloc1 starts at 1.
///
/// assert_eq!(guard.load(index).copied(), Some("foo"));
///
/// let bar = match guard.try_insert(index, bar, GFP_KERNEL) {
///     Ok(()) => panic!("try_insert({index}) succeeded while occupied"),
///     Err((bar, err)) => {
///         assert_eq!(err, EBUSY);
///         bar
///     }
/// };
///
/// let (reservation1, reservation1_index) = guard.reserve_limit(.., GFP_KERNEL)?;
/// let (reservation2, reservation2_index) = guard.reserve_limit(.., GFP_KERNEL)?;
///
/// let foo = guard.erase(index).unwrap();
/// assert_eq!(*foo, "foo");
///
/// drop(guard); // Reservations can outlive the guard.
///
/// assert_eq!(reservation1.fill(foo).unwrap().as_deref(), None);
///
/// let mut guard = xa.lock();
///
/// let bar = match guard.try_insert(reservation2_index, bar, GFP_KERNEL) {
///     Ok(()) => panic!("try_insert({reservation2_index}) succeeded while reserved"),
///     Err((bar, err)) => {
///         assert_eq!(err, EBUSY);
///         bar
///     }
/// };
///
/// // `store` ignores reservations.
/// assert_eq!(
///     guard
///         .store(reservation2_index, bar, GFP_KERNEL)
///         .unwrap()
///         .as_deref(),
///     None
/// );
///
/// assert_eq!(guard.load(reservation2_index).copied(), Some("bar"));
///
/// // Reservations are filled using `store`, so they overwrite existing entries.
/// let bar = reservation2.fill_locked(&mut guard, baz).unwrap().unwrap();
///
/// assert_eq!(guard.load(reservation2_index).copied(), Some("baz"));
///
/// # Ok::<(), Error>(())
/// ```
#[pin_data(PinnedDrop)]
pub struct XArray<T: ForeignOwnable> {
    #[pin]
    xa: Opaque<bindings::xarray>,
    _p: PhantomData<T>,
}

#[pinned_drop]
impl<T: ForeignOwnable> PinnedDrop for XArray<T> {
    fn drop(self: Pin<&mut Self>) {
        self.iter_inner().for_each(|ptr| {
            let ptr = ptr.as_ptr();
            // SAFETY: `ptr` came from `T::into_foreign`.
            //
            // SAFETY: `self` statically owns the only reference to the array.
            drop(unsafe { T::from_foreign(ptr) })
        });

        // SAFETY: `self` statically owns the only reference to the array.
        unsafe { bindings::xa_destroy(self.xa.get()) };
    }
}

/// Flags passed to [`XArray::new`] to configure the array's allocation tracking behavior.
pub enum AllocKind {
    /// Consider the first element to be at index 0.
    Alloc,
    /// Consider the first element to be at index 1.
    Alloc1,
}

impl<T: ForeignOwnable> XArray<T> {
    /// Creates a new [`XArray`].
    pub fn new(kind: AllocKind) -> impl PinInit<Self> {
        let flags = match kind {
            AllocKind::Alloc => bindings::XA_FLAGS_ALLOC,
            AllocKind::Alloc1 => bindings::XA_FLAGS_ALLOC1,
        };
        pin_init!(Self {
            // SAFETY: `xa` is valid while the closure is called.
            xa <- Opaque::ffi_init(|xa| unsafe {
                bindings::xa_init_flags(xa, flags)
            }),
            _p: PhantomData,
        })
    }

    fn iter_inner(&self) -> impl Iterator<Item = core::ptr::NonNull<T::PointedTo>> + '_ {
        let mut index = c_ulong::MAX;

        // SAFETY: `self.xa` is always valid by the type invariant.
        iter::once(unsafe {
            bindings::xa_find(
                self.xa.get(),
                &mut index,
                c_ulong::MAX,
                bindings::XA_PRESENT,
            )
        })
        .chain(iter::from_fn(move || {
            // SAFETY: `self.xa` is always valid by the type invariant.
            Some(unsafe {
                bindings::xa_find_after(
                    self.xa.get(),
                    &mut index,
                    c_ulong::MAX,
                    bindings::XA_PRESENT,
                )
            })
        }))
        .map_while(|ptr| core::ptr::NonNull::new(ptr.cast()))
    }

    /// Returns an iterator over the entries in the array.
    pub fn iter(&self) -> impl Iterator<Item = T::Borrowed<'_>> {
        self.iter_inner().map(|ptr| {
            let ptr = ptr.as_ptr();
            // SAFETY: `ptr` came from `T::into_foreign`.
            unsafe { T::borrow(ptr) }
        })
    }
}

// NB: This is a separate impl block because it morally doesn't rely on the `ForeignOwnable` trait
// bound. In practice the bound is required to be at the type level by the implementation of the
// `pinned_drop` attribute. Note that it would also be required by a "normal" Drop implementation.
impl<T: ForeignOwnable> XArray<T> {
    /// Attempts to lock the [`XArray`] for exclusive access.
    pub fn try_lock(&self) -> Option<Guard<'_, T>> {
        // SAFETY: `self.xa` is always valid by the type invariant.
        (unsafe { bindings::xa_trylock(self.xa.get()) } != 0).then(|| Guard { xa: self })
    }

    /// Locks the [`XArray`] for exclusive access.
    pub fn lock(&self) -> Guard<'_, T> {
        // SAFETY: `self.xa` is always valid by the type invariant.
        unsafe { bindings::xa_lock(self.xa.get()) };

        Guard { xa: self }
    }
}

/// A lock guard.
///
/// The lock is unlocked when the guard goes out of scope.
#[must_use = "the lock unlocks immediately when the guard is unused"]
pub struct Guard<'a, T: ForeignOwnable> {
    xa: &'a XArray<T>,
}

impl<T: ForeignOwnable> Drop for Guard<'_, T> {
    fn drop(&mut self) {
        // SAFETY: The caller owns the lock, so it is safe to unlock it.
        unsafe { bindings::xa_unlock(self.xa.xa.get()) };
    }
}

fn to_index(i: usize) -> c_ulong {
    i.try_into()
        .unwrap_or_else(|_| build_error!("cannot convert usize to c_ulong"))
}

fn to_usize(i: u32) -> usize {
    i.try_into()
        .unwrap_or_else(|_| build_error!("cannot convert u32 to usize"))
}

impl<'a, T: ForeignOwnable> Guard<'a, T> {
    /// Loads an entry from the array.
    ///
    /// Returns the entry at the given index.
    pub fn load(&mut self, index: usize) -> Option<T::Borrowed<'_>> {
        // SAFETY: `self.xa` is always valid by the type invariant.
        let ptr = unsafe { bindings::xa_load(self.xa.xa.get(), to_index(index)) };
        (!ptr.is_null()).then(|| {
            let ptr = ptr.cast();

            // SAFETY: `ptr` is either NULL or came from `T::into_foreign`.
            //
            // SAFETY: `self` statically owns the only reference to the array.
            unsafe { T::borrow(ptr) }
        })
    }

    /// Erases an entry from the array.
    ///
    /// Returns the entry which was previously at the given index.
    pub fn erase(&mut self, index: usize) -> Option<T> {
        // SAFETY: `self.xa` is always valid by the type invariant.
        //
        // SAFETY: `self` statically owns the only reference to the array.
        let ptr = unsafe { bindings::__xa_erase(self.xa.xa.get(), to_index(index)) }.cast();
        // SAFETY: `ptr` is either NULL or came from `T::into_foreign`.
        unsafe { T::try_from_foreign(ptr) }
    }

    /// Stores an entry in the array.
    ///
    /// On success, returns the entry which was previously at the given index.
    ///
    /// On failure, returns the entry which was attempted to be stored.
    pub fn store(
        &mut self,
        index: usize,
        value: T,
        gfp: alloc::Flags,
    ) -> Result<Option<T>, (T, Error)> {
        build_assert!(
            mem::align_of::<T::PointedTo>() >= 4,
            "pointers stored in XArray must be 4-byte aligned"
        );
        let new = value.into_foreign();

        let old = {
            let new = new.cast();
            // SAFETY: `self.xa` is always valid by the type invariant.
            //
            // SAFETY: `self` statically owns the only reference to the array.
            //
            // INVARIANT: `new` came from `T::into_foreign`.
            unsafe { bindings::__xa_store(self.xa.xa.get(), to_index(index), new, gfp.as_raw()) }
        };

        // SAFETY: `__xa_store` returns the old entry at this index on success or `xa_err` if an
        // error happened.
        match unsafe { bindings::xa_err(old) } {
            0 => {
                let old = old.cast();
                // SAFETY: `ptr` is either NULL or came from `T::into_foreign`.
                Ok(unsafe { T::try_from_foreign(old) })
            }
            errno => {
                // SAFETY: `new` came from `T::into_foreign` and `__xa_store` does not take
                // ownership of the value on error.
                let value = unsafe { T::from_foreign(new) };
                Err((value, Error::from_errno(errno)))
            }
        }
    }

    /// Stores an entry in the array if no entry is present.
    pub fn try_insert(
        &mut self,
        index: usize,
        value: T,
        gfp: alloc::Flags,
    ) -> Result<(), (T, Error)> {
        build_assert!(
            mem::align_of::<T::PointedTo>() >= 4,
            "pointers stored in XArray must be 4-byte aligned"
        );
        let ptr = value.into_foreign();

        // SAFETY: `self.xa` is always valid by the type invariant.
        //
        // INVARIANT: `ptr` came from `T::into_foreign`.
        //
        // NB: it may seem that this could be implemented in terms of `__xa_cmpxchg`, but that
        // function returns XA_ZERO_ENTRY as NULL, making it impossible for the caller to know
        // whether a reservation previously existed.
        match unsafe {
            bindings::__xa_insert(self.xa.xa.get(), to_index(index), ptr.cast(), gfp.as_raw())
        } {
            0 => Ok(()),
            errno => {
                // SAFETY: `ptr` came from `T::into_foreign` and `__xa_insert` does not take
                // ownership of the value on error.
                let value = unsafe { T::from_foreign(ptr) };
                Err((value, Error::from_errno(errno)))
            }
        }
    }

    /// Wrapper around `__xa_alloc`.
    ///
    /// On success, takes ownership of pointers passed in `op`.
    ///
    /// On failure, ownership returns to the caller.
    ///
    /// # Safety
    ///
    /// `ptr` must be NULL or have come from a previous call to `T::into_foreign`.
    unsafe fn alloc(
        &mut self,
        limit: impl ops::RangeBounds<u32>,
        ptr: *mut T::PointedTo,
        gfp: alloc::Flags,
    ) -> Result<usize, Error> {
        // NB: `xa_limit::{max,min}` are inclusive.
        let limit = bindings::xa_limit {
            max: match limit.end_bound() {
                ops::Bound::Included(&end) => end,
                ops::Bound::Excluded(&end) => end - 1,
                ops::Bound::Unbounded => u32::MAX,
            },
            min: match limit.start_bound() {
                ops::Bound::Included(&start) => start,
                ops::Bound::Excluded(&start) => start + 1,
                ops::Bound::Unbounded => 0,
            },
        };

        let mut index = u32::MAX;

        // SAFETY: `self.xa` is always valid by the type invariant.
        //
        // SAFETY: `self` statically owns the only reference to the array.
        //
        // INVARIANT: `self.xa` was initialized with `XA_FLAGS_ALLOC`.
        //
        // INVARIANT: `ptr` is either NULL or came from `T::into_foreign`.
        let result = unsafe {
            bindings::__xa_alloc(
                self.xa.xa.get(),
                &mut index,
                ptr.cast(),
                limit,
                gfp.as_raw(),
            )
        };

        // NB: `__xa_alloc` returns 0 on success or `errno` if an error happened.
        match result {
            0 => Ok(to_usize(index)),
            errno => Err(Error::from_errno(errno)),
        }
    }

    /// Allocates an entry somewhere in the array.
    ///
    /// On success, returns the index at which the entry was stored.
    ///
    /// On failure, returns the entry which was attempted to be stored.
    pub fn insert_limit(
        &mut self,
        limit: impl ops::RangeBounds<u32>,
        value: T,
        gfp: alloc::Flags,
    ) -> Result<usize, (T, Error)> {
        build_assert!(
            mem::align_of::<T::PointedTo>() >= 4,
            "pointers stored in XArray must be 4-byte aligned"
        );
        let ptr = value.into_foreign();

        // SAFETY: `ptr` came from `T::into_foreign`.
        unsafe { self.alloc(limit, ptr, gfp) }.map_err(|err| {
            // SAFETY: `ptr` came from `T::into_foreign` and `self.alloc` does not take ownership of
            // the value on error.
            let value = unsafe { T::from_foreign(ptr) };
            (value, err)
        })
    }

    /// Reserves an entry in the array.
    pub fn reserve(
        &mut self,
        index: usize,
        gfp: alloc::Flags,
    ) -> Result<Reservation<'a, T>, Error> {
        let ptr = core::ptr::null_mut();
        // SAFETY: `self.xa` is always valid by the type invariant.
        //
        // INVARIANT: `ptr` came from `T::into_foreign`.
        //
        // NB: it may seem that this could be implemented in terms of `__xa_cmpxchg`, but that
        // function returns XA_ZERO_ENTRY as NULL, making it impossible for the caller to know
        // whether a reservation previously existed.
        match unsafe { bindings::__xa_insert(self.xa.xa.get(), to_index(index), ptr, gfp.as_raw()) }
        {
            0 => Ok(Reservation { xa: self.xa, index }),
            errno => Err(Error::from_errno(errno)),
        }
    }

    /// Reserves an entry somewhere in the array.
    pub fn reserve_limit(
        &mut self,
        limit: impl ops::RangeBounds<u32>,
        gfp: alloc::Flags,
    ) -> Result<(Reservation<'a, T>, usize), Error> {
        let ptr = core::ptr::null_mut();
        // SAFETY: `ptr` is NULL.
        unsafe { self.alloc(limit, ptr, gfp) }
            .map(|index| (Reservation { xa: self.xa, index }, index))
    }
}

/// A reserved slot in an array.
///
/// The slot is released when the reservation goes out of scope.
///
/// Note that the array lock *must not* be held when the reservation is filled or dropped as this
/// will lead to deadlock. [`Reservation::insert_locked`] and [`Reservation::release_locked`] can be
/// used in context where the array lock is held.
pub struct Reservation<'a, T: ForeignOwnable> {
    xa: &'a XArray<T>,
    index: usize,
}

impl<T: ForeignOwnable> Reservation<'_, T> {
    fn fill_inner(
        guard: &mut Guard<'_, T>,
        index: usize,
        value: T,
    ) -> Result<Option<T>, (T, Error)> {
        // NB: it may seem that this could be implemented in terms of `__xa_cmpxchg`, but that
        // function returns XA_ZERO_ENTRY as NULL, making it impossible for the caller to know
        // whether a reservation previously existed.
        guard.store(index, value, alloc::Flags::empty())
    }

    fn release_inner(guard: &mut Guard<'_, T>, index: usize) -> Result<(), Error> {
        // SAFETY: `xa_zero_entry` wraps XA_ZERO_ENTRY which is always safe to use.
        let xa_zero_entry = unsafe { bindings::xa_zero_entry() };
        let ptr = core::ptr::null_mut();
        // SAFETY: `self.xa` is always valid by the type invariant.
        //
        // SAFETY: `self` statically owns the only reference to the array.
        //
        // INVARIANT: `xa_zero_entry` is converted to NULL on the egress path of all XArray
        // functions in the "normal" API; only `__xa_cmpxchg` distinguishes between NULL and
        // `xa_zero_entry` and only on its *ingress* path.
        //
        // INVARIANT: `ptr` is `NULL`.
        let old = unsafe {
            bindings::__xa_cmpxchg(guard.xa.xa.get(), to_index(index), xa_zero_entry, ptr, 0)
        };

        // SAFETY: `__xa_cmpxchg` returns the old entry at this index on success or `xa_err` if an
        // error happened.
        match unsafe { bindings::xa_err(old) } {
            0 => {
                // NB: `__xa_cmpxchg` returns the old entry at this index regardless of whether a
                // replacement was made. It also returns `xa_zero_entry` as NULL. This means it is
                // impossible to determine whether the reservation was released by this operation
                // though if `old` is not NULL then it means the reservation was `store`d over.
                Ok(())
            }
            errno => Err(Error::from_errno(errno)),
        }
    }

    /// Fills the reservation.
    pub fn fill(self, value: T) -> Result<Option<T>, (T, Error)> {
        let Self { xa, index } = &self;
        let index = *index;
        let mut guard = xa.lock();

        mem::forget(self);
        Self::fill_inner(&mut guard, index, value)
    }

    /// Fills the reservation without acquiring the array lock.
    ///
    /// # Panics
    ///
    /// Panics if the passed guard locks a different array.
    pub fn fill_locked(self, guard: &mut Guard<'_, T>, value: T) -> Result<Option<T>, (T, Error)> {
        let Self { xa, index } = &self;
        let index = *index;
        assert_eq!(guard.xa.xa.get(), xa.xa.get());

        mem::forget(self);
        Self::fill_inner(guard, index, value)
    }

    /// Releases the reservation without acquiring the array lock.
    ///
    /// # Panics
    ///
    /// Panics if the passed guard locks a different array.
    pub fn release_locked(self, guard: &mut Guard<'_, T>) -> Result<(), Error> {
        let Self { xa, index } = &self;
        let index = *index;
        assert_eq!(guard.xa.xa.get(), xa.xa.get());

        mem::forget(self);
        Self::release_inner(guard, index)
    }
}

impl<T: ForeignOwnable> Drop for Reservation<'_, T> {
    fn drop(&mut self) {
        let Self { xa, index } = self;

        let mut guard = xa.lock();

        // NB: Errors here are possible since `Guard::store` does not honor reservations.
        let _: Result<(), Error> = Self::release_inner(&mut guard, *index);
    }
}

// SAFETY: It is safe to send `XArray<T>` to another thread when the underlying `T` is `Send`
// because XArray is thread-safe and all mutation operations are synchronized.
unsafe impl<T: ForeignOwnable + Send> Send for XArray<T> {}

// SAFETY: It is safe to send `&XArray<T>` to another thread when the underlying `T` is `Sync`
// because it effectively means sharing `&T` (which is safe because `T` is `Sync`). Additionally,
// `T` is `Send` because XArray is thread-safe and all mutation operations are internally locked.
unsafe impl<T: ForeignOwnable + Send + Sync> Sync for XArray<T> {}
