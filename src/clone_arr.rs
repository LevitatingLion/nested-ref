//! Utility for cloning a [`GenericArray`] of [`Ref`]s

use core::{
    cell::Ref,
    mem::{self, ManuallyDrop, MaybeUninit},
    slice,
};

use generic_array::{ArrayLength, GenericArray};

/// Clones a [`GenericArray`] of [`Ref`]s
#[must_use]
#[inline]
pub fn clone_arr<'a, T, N>(orig: &GenericArray<Ref<'a, T>, N>) -> GenericArray<Ref<'a, T>, N>
where
    T: ?Sized,
    N: ArrayLength<Ref<'a, T>>,
{
    // This can also be implemented in safe code, using something like
    // `GenericArray::from_exact_iter(self.outer.iter().map(Ref::clone))`. However, doing it
    // manually generates better code.

    // Allocate uninitialized memory for the return value
    let mut arr = MaybeUninit::<GenericArray<Ref<'a, T>, N>>::uninit();

    // Create a slice of `MaybeUninit`, to be able to initialize the elements one by one
    let data = arr.as_mut_ptr().cast::<MaybeUninit<Ref<'a, T>>>();
    let len = N::to_usize();
    // Safety: `GenericArray<T, N>` has the same layout as `[T; N]`, which has the same layout
    // as `[MaybeUninit<T>; N]`.
    let slice = unsafe { slice::from_raw_parts_mut(data, len) };

    // Create a dropper for the initialized part of our array, so we don't leak any
    // already-initialized `Ref`s in the case that `Ref::clone` panics
    let mut dropper = PartialArrayDropper::new(data.cast::<Ref<'a, T>>());

    // Iterate over all array elements
    for (old, new) in orig.iter().zip(slice) {
        // Initialize this element with a clone of the corresponding original element
        new.write(Ref::clone(old));
        // Prime this element for dropping, in case `Ref::clone` panics on subsequent
        // iterations. Safety: We just initialized this element, it's valid for dropping.
        unsafe { dropper.prime_next() };
    }

    // Defuse the dropper so we can safely return the array
    dropper.defuse();
    // Safety: The array is fully initialized
    unsafe { arr.assume_init() }
}

/// Ensures that some prefix of an array's elements is dropped
struct PartialArrayDropper<T> {
    /// Pointer to the first element of the array
    data: *mut T,
    /// Number of array elements that are primed for dropping
    len:  usize,
}

impl<T> PartialArrayDropper<T> {
    /// Creates a new dropper for an array, given a pointer to its first element.
    /// [`prime_next`](Self::prime_next) needs to be called to actually prime elements for dropping.
    #[must_use]
    #[inline]
    pub const fn new(data: *mut T) -> Self {
        let len = 0;
        Self { data, len }
    }

    /// Primes the next array element for dropping.
    ///
    /// # Safety
    ///
    /// It must be legal to drop the next array element. In particular, a pointer to it must be
    /// *valid* for reads and writes and properly aligned, and any type-dependent invariants must
    /// hold. See the documentation of [`drop_in_place`](core::ptr::drop_in_place) for more
    /// information.
    #[inline]
    pub unsafe fn prime_next(&mut self) {
        self.len += 1;
    }

    /// Consumes the dropper without dropping any array elements
    #[inline]
    pub const fn defuse(self) {
        mem::forget(self);
    }
}

impl<T> Drop for PartialArrayDropper<T> {
    #[inline]
    fn drop(&mut self) {
        // Treat the array as an array of `ManuallyDrop<T>`. `T` and `ManuallyDrop<T>` have the same
        // layout, so the resulting pointer is valid.
        let data = self.data.cast::<ManuallyDrop<T>>();
        // Obtain a slice of all the elements we want to drop. Safety: The caller of `prime_next`
        // ensured that all these elements are valid.
        let slice = unsafe { slice::from_raw_parts_mut(data, self.len) };
        for elem in slice {
            // Drop each element. Safety: The caller of `prime_next` ensured that all these elements
            // can be dropped.
            unsafe { ManuallyDrop::drop(elem) };
        }
    }
}
