// SPDX-License-Identifier: GPL-2.0

//! XArray abstraction.
//!
//! C header: [`include/linux/xarray.h`](srctree/include/linux/xarray.h)

use crate::{
    alloc, bindings, build_assert, build_error,
    error::Error,
    types::{ForeignOwnable, NotThreadSafe, Opaque},
};
use core::{iter, marker::PhantomData, mem, ops, pin::Pin, ptr::NonNull};
use pin_init::{pin_data, pin_init, pinned_drop, PinInit};

/// An array which efficiently maps sparse integer indices to owned objects.
///
/// This is similar to a [`crate::alloc::kvec::Vec<Option<T>>`], but more efficient when there are
/// holes in the index space, and can be efficiently grown.
///
/// # Invariants
///
/// `self.xa` is always an initialized and valid [`bindings::xarray`] whose entries are either
/// `XA_ZERO_ENTRY` or came from `T::into_foreign`.
///
/// # Examples
///
/// ```rust
/// use kernel::alloc::KBox;
/// use kernel::xarray::{AllocKind, StoreError, XArray};
///
/// let xa = KBox::pin_init(XArray::new(AllocKind::Alloc1), GFP_KERNEL)?;
///
/// let dead = KBox::new(0xdead, GFP_KERNEL)?;
/// let beef = KBox::new(0xbeef, GFP_KERNEL)?;
/// let leet = KBox::new(0x1337, GFP_KERNEL)?;
///
/// let mut guard = xa.lock();
///
/// let index = guard.insert_limit(.., dead, GFP_KERNEL)?;
/// assert_eq!(index, 1); // AllocKind::Alloc1 starts at 1.
///
/// assert_eq!(guard.get(index).copied(), Some(0xdead));
///
/// let beef = match guard.try_insert(index, beef, GFP_KERNEL) {
///     Ok(()) => panic!("try_insert({index}) succeeded while occupied"),
///     Err(StoreError { value, error }) => {
///         assert_eq!(error, EBUSY);
///         value
///     }
/// };
///
/// let (reservation1, reservation1_index) = guard.reserve_limit(.., GFP_KERNEL)?;
/// let (reservation2, reservation2_index) = guard.reserve_limit(.., GFP_KERNEL)?;
///
/// let dead = guard.remove(index).unwrap();
/// assert_eq!(*dead, 0xdead);
///
/// drop(guard); // Reservations can outlive the guard.
///
/// assert_eq!(reservation1.fill(dead)?.as_deref(), None);
///
/// let mut guard = xa.lock();
///
/// let beef = match guard.try_insert(reservation2_index, beef, GFP_KERNEL) {
///     Ok(()) => panic!("try_insert({reservation2_index}) succeeded while reserved"),
///     Err(StoreError { value, error }) => {
///         assert_eq!(error, EBUSY);
///         value
///     }
/// };
///
/// // `store` ignores reservations.
/// assert_eq!(
///     guard
///         .store(reservation2_index, beef, GFP_KERNEL)?
///         .as_deref(),
///     None
/// );
///
/// assert_eq!(guard.get(reservation2_index).copied(), Some(0xbeef));
///
/// // Reservations are filled using `store`, so they overwrite existing entries.
/// let beef = reservation2.fill_locked(&mut guard, leet)?.unwrap();
/// assert_eq!(*beef, 0xbeef);
///
/// assert_eq!(guard.get(reservation2_index).copied(), Some(0x1337));
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
        self.iter().for_each(|ptr| {
            let ptr = ptr.as_ptr();
            // SAFETY: `ptr` came from `T::into_foreign`.
            //
            // INVARIANT: we own the only reference to the array which is being dropped so the
            // broken invariant is not observable on function exit.
            drop(unsafe { T::from_foreign(ptr) })
        });

        // SAFETY: `self.xa` is always valid by the type invariant.
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
    /// Creates a new initializer for this type.
    pub fn new(kind: AllocKind) -> impl PinInit<Self> {
        let flags = match kind {
            AllocKind::Alloc => bindings::XA_FLAGS_ALLOC,
            AllocKind::Alloc1 => bindings::XA_FLAGS_ALLOC1,
        };
        pin_init!(Self {
            // SAFETY: `xa` is valid while the closure is called.
            //
            // INVARIANT: `xa` is initialized here to an empty, valid [`bindings::xarray`].
            xa <- Opaque::ffi_init(|xa| unsafe {
                bindings::xa_init_flags(xa, flags)
            }),
            _p: PhantomData,
        })
    }

    fn iter(&self) -> impl Iterator<Item = NonNull<T::PointedTo>> + '_ {
        let mut index = 0;

        // SAFETY: `self.xa` is always valid by the type invariant.
        iter::once(unsafe {
            bindings::xa_find(self.xa.get(), &mut index, usize::MAX, bindings::XA_PRESENT)
        })
        .chain(iter::from_fn(move || {
            // SAFETY: `self.xa` is always valid by the type invariant.
            Some(unsafe {
                bindings::xa_find_after(self.xa.get(), &mut index, usize::MAX, bindings::XA_PRESENT)
            })
        }))
        .map_while(|ptr| NonNull::new(ptr.cast()))
    }

    /// Attempts to lock the [`XArray`] for exclusive access.
    pub fn try_lock(&self) -> Option<Guard<'_, T>> {
        // SAFETY: `self.xa` is always valid by the type invariant.
        if (unsafe { bindings::xa_trylock(self.xa.get()) } != 0) {
            Some(Guard {
                xa: self,
                _not_send: NotThreadSafe,
            })
        } else {
            None
        }
    }

    /// Locks the [`XArray`] for exclusive access.
    pub fn lock(&self) -> Guard<'_, T> {
        // SAFETY: `self.xa` is always valid by the type invariant.
        unsafe { bindings::xa_lock(self.xa.get()) };

        Guard {
            xa: self,
            _not_send: NotThreadSafe,
        }
    }
}

/// A lock guard.
///
/// The lock is unlocked when the guard goes out of scope.
#[must_use = "the lock unlocks immediately when the guard is unused"]
pub struct Guard<'a, T: ForeignOwnable> {
    xa: &'a XArray<T>,
    _not_send: NotThreadSafe,
}

impl<T: ForeignOwnable> Drop for Guard<'_, T> {
    fn drop(&mut self) {
        // SAFETY:
        // - `self.xa.xa` is always valid by the type invariant.
        // - The caller holds the lock, so it is safe to unlock it.
        unsafe { bindings::xa_unlock(self.xa.xa.get()) };
    }
}

/// The error returned by [`store`](Guard::store).
///
/// Contains the underlying error and the value that was not stored.
pub struct StoreError<T> {
    /// The error that occurred.
    pub error: Error,
    /// The value that was not stored.
    pub value: T,
}

impl<T> From<StoreError<T>> for Error {
    fn from(value: StoreError<T>) -> Self {
        value.error
    }
}

fn to_usize(i: u32) -> usize {
    i.try_into()
        .unwrap_or_else(|_| build_error!("cannot convert u32 to usize"))
}

impl<'a, T: ForeignOwnable> Guard<'a, T> {
    fn load<F, U>(&self, index: usize, f: F) -> Option<U>
    where
        F: FnOnce(NonNull<T::PointedTo>) -> U,
    {
        // SAFETY: `self.xa.xa` is always valid by the type invariant.
        let ptr = unsafe { bindings::xa_load(self.xa.xa.get(), index) };
        let ptr = NonNull::new(ptr.cast())?;
        Some(f(ptr))
    }

    /// Provides a reference to the element at the given index.
    pub fn get(&self, index: usize) -> Option<T::Borrowed<'_>> {
        self.load(index, |ptr| {
            // SAFETY: `ptr` came from `T::into_foreign`.
            unsafe { T::borrow(ptr.as_ptr()) }
        })
    }

    /// Provides a mutable reference to the element at the given index.
    pub fn get_mut(&mut self, index: usize) -> Option<T::BorrowedMut<'_>> {
        self.load(index, |ptr| {
            // SAFETY: `ptr` came from `T::into_foreign`.
            unsafe { T::borrow_mut(ptr.as_ptr()) }
        })
    }

    /// Removes and returns the element at the given index.
    pub fn remove(&mut self, index: usize) -> Option<T> {
        // SAFETY:
        // - `self.xa.xa` is always valid by the type invariant.
        // - The caller holds the lock.
        let ptr = unsafe { bindings::__xa_erase(self.xa.xa.get(), index) }.cast();
        // SAFETY:
        // - `ptr` is either NULL or came from `T::into_foreign`.
        // - `&mut self` guarantees that the lifetimes of [`T::Borrowed`] and [`T::BorrowedMut`]
        // borrowed from `self` have ended.
        unsafe { T::try_from_foreign(ptr) }
    }

    /// Stores an element at the given index.
    ///
    /// May drop the lock if needed to allocate memory, and then reacquire it afterwards.
    ///
    /// On success, returns the element which was previously at the given index.
    ///
    /// On failure, returns the element which was attempted to be stored.
    pub fn store(
        &mut self,
        index: usize,
        value: T,
        gfp: alloc::Flags,
    ) -> Result<Option<T>, StoreError<T>> {
        build_assert!(
            mem::align_of::<T::PointedTo>() >= 4,
            "pointers stored in XArray must be 4-byte aligned"
        );
        let new = value.into_foreign();

        let old = {
            let new = new.cast();
            // SAFETY:
            // - `self.xa.xa` is always valid by the type invariant.
            // - The caller holds the lock.
            //
            // INVARIANT: `new` came from `T::into_foreign`.
            unsafe { bindings::__xa_store(self.xa.xa.get(), index, new, gfp.as_raw()) }
        };

        // SAFETY: `__xa_store` returns the old entry at this index on success or `xa_err` if an
        // error happened.
        let errno = unsafe { bindings::xa_err(old) };
        if errno != 0 {
            // SAFETY: `new` came from `T::into_foreign` and `__xa_store` does not take
            // ownership of the value on error.
            let value = unsafe { T::from_foreign(new) };
            Err(StoreError {
                value,
                error: Error::from_errno(errno),
            })
        } else {
            let old = old.cast();
            // SAFETY: `ptr` is either NULL or came from `T::into_foreign`.
            //
            // NB: `XA_ZERO_ENTRY` is never returned by functions belonging to the Normal XArray
            // API; such entries present as `NULL`.
            Ok(unsafe { T::try_from_foreign(old) })
        }
    }

    /// Stores an entry in the array if no entry is present.
    pub fn try_insert(
        &mut self,
        index: usize,
        value: T,
        gfp: alloc::Flags,
    ) -> Result<(), StoreError<T>> {
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
        match unsafe { bindings::__xa_insert(self.xa.xa.get(), index, ptr.cast(), gfp.as_raw()) } {
            0 => Ok(()),
            errno => {
                // SAFETY: `ptr` came from `T::into_foreign` and `__xa_insert` does not take
                // ownership of the value on error.
                let value = unsafe { T::from_foreign(ptr) };
                Err(StoreError {
                    value,
                    error: Error::from_errno(errno),
                })
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
    ) -> Result<usize, StoreError<T>> {
        build_assert!(
            mem::align_of::<T::PointedTo>() >= 4,
            "pointers stored in XArray must be 4-byte aligned"
        );
        let ptr = value.into_foreign();

        // SAFETY: `ptr` came from `T::into_foreign`.
        unsafe { self.alloc(limit, ptr, gfp) }.map_err(|error| {
            // SAFETY: `ptr` came from `T::into_foreign` and `self.alloc` does not take ownership of
            // the value on error.
            let value = unsafe { T::from_foreign(ptr) };
            StoreError { value, error }
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
        match unsafe { bindings::__xa_insert(self.xa.xa.get(), index, ptr, gfp.as_raw()) } {
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
    ) -> Result<Option<T>, StoreError<T>> {
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
        let old =
            unsafe { bindings::__xa_cmpxchg(guard.xa.xa.get(), index, xa_zero_entry, ptr, 0) };

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
    pub fn fill(self, value: T) -> Result<Option<T>, StoreError<T>> {
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
    pub fn fill_locked(
        self,
        guard: &mut Guard<'_, T>,
        value: T,
    ) -> Result<Option<T>, StoreError<T>> {
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

// SAFETY: `XArray<T>` has no shared mutable state so it is `Send` iff `T` is `Send`.
unsafe impl<T: ForeignOwnable + Send> Send for XArray<T> {}

// SAFETY: `XArray<T>` serialises the interior mutability it provides so it is `Sync` iff `T` is
// `Send`.
unsafe impl<T: ForeignOwnable + Send> Sync for XArray<T> {}
