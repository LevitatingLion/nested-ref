//! Shared reference to data contained in one or more nested [`RefCell`]s

#[cfg(doc)]
use core::cell::RefCell;
use core::{
    cell::{Ref, RefMut},
    ops::{Add, Deref},
    ptr::addr_of,
};

use generic_array::{
    arr,
    sequence::Lengthen,
    typenum::{Add1, B1, U0},
    ArrayLength, GenericArray,
};

use crate::{clone_arr::clone_arr, NestedRefMut};

/// Shared reference to data contained in one or more nested [`RefCell`]s.
///
/// This has the same interface as [`Ref`], with the additional methods
/// [`map_ref`](NestedRef::map_ref) and [`map_ref_mut`](NestedRef::map_ref_mut) that form references
/// into nested [`RefCell`]s.
///
/// # Examples
///
/// ```
/// # use std::cell::{Cell, RefCell};
/// # use nested_ref::NestedRef;
/// // Create a `RefCell` two levels deep and a `NestedRef` into it
/// let rc = RefCell::new(RefCell::new(Cell::new(0)));
/// let nr = NestedRef::new(rc.borrow());
/// let nr = NestedRef::map_ref(nr, RefCell::borrow);
/// assert_eq!(nr.get(), 0);
///
/// // Mutate through `NestedRef`
/// nr.set(1);
/// assert_eq!(nr.get(), 1);
///
/// // Mutate through independent `Ref`
/// rc.borrow().borrow().set(2);
/// assert_eq!(nr.get(), 2);
/// ```
pub struct NestedRef<'a, T, N>
where
    T: ?Sized,
    N: ArrayLength<Ref<'a, ()>>,
{
    /// Reference into the innermost [`RefCell`]
    inner: Ref<'a, T>,
    /// Type-erased references into the other [`RefCell`]s, from outermost to innermost
    // We store a `&()` in each array entry. It would be better to store the internal `BorrowRef`
    // directly, but that's not exposed.
    outer: GenericArray<Ref<'a, ()>, N>,
}

impl<'a, T> NestedRef<'a, T, U0>
where
    T: ?Sized,
{
    /// Creates a new reference inside a single [`RefCell`]
    #[must_use]
    #[inline]
    pub fn new(inner: Ref<'a, T>) -> Self {
        // Start with an empty array of outer `Ref`s
        let outer = arr![Ref<'a, ()>;];
        Self { inner, outer }
    }
}

impl<'a, T, N> NestedRef<'a, T, N>
where
    T: ?Sized,
    N: ArrayLength<Ref<'a, ()>>,
{
    /// Clones the reference, like [`Ref::clone`].
    ///
    /// This is an associated function, because a method would interfere with methods of the same
    /// name on the contents of the [`RefCell`].
    #[must_use]
    #[inline]
    #[allow(clippy::should_implement_trait)]
    pub fn clone(orig: &Self) -> Self {
        // Just clone all contained `Ref`s
        Self {
            inner: Ref::clone(&orig.inner),
            outer: clone_arr(&orig.outer),
        }
    }

    /// Creates a reference to a component of the borrowed data, like [`Ref::map`].
    ///
    /// This is an associated function, because a method would interfere with methods of the same
    /// name on the contents of the [`RefCell`].
    #[inline]
    pub fn map<U, F>(orig: Self, f: F) -> NestedRef<'a, U, N>
    where
        U: ?Sized,
        F: FnOnce(&T) -> &U,
    {
        // Outer `Ref` is type-erased, so just map the inner `Ref`
        NestedRef {
            inner: Ref::map(orig.inner, f),
            outer: orig.outer,
        }
    }

    /// Creates a reference to an optional component of the borrowed data, like [`Ref::filter_map`].
    /// The original reference is returned inside an `Err` if the closure returns `None`.
    ///
    /// This is an associated function, because a method would interfere with methods of the same
    /// name on the contents of the [`RefCell`].
    #[inline]
    #[allow(clippy::missing_errors_doc)]
    pub fn filter_map<U, F>(orig: Self, f: F) -> Result<NestedRef<'a, U, N>, Self>
    where
        U: ?Sized,
        F: FnOnce(&T) -> Option<&U>,
    {
        // Outer `Ref`s remain the same
        let outer = orig.outer;
        // Delegate to inner `Ref` and put the result back together
        match Ref::filter_map(orig.inner, f) {
            Ok(inner) => Ok(NestedRef { inner, outer }),
            Err(inner) => Err(NestedRef { inner, outer }),
        }
    }

    /// Splits a reference into multiple references for different components of the borrowed data,
    /// like [`Ref::map_split`].
    ///
    /// This is an associated function, because a method would interfere with methods of the same
    /// name on the contents of the [`RefCell`].
    #[inline]
    pub fn map_split<U, V, F>(orig: Self, f: F) -> (NestedRef<'a, U, N>, NestedRef<'a, V, N>)
    where
        U: ?Sized,
        V: ?Sized,
        F: FnOnce(&T) -> (&U, &V),
    {
        // We need the outer `Ref`s two times
        let outer_a = clone_arr(&orig.outer);
        let outer_b = orig.outer;
        // Delegate to inner `Ref` and put the results back together
        let (inner_a, inner_b) = Ref::map_split(orig.inner, f);
        (
            NestedRef {
                inner: inner_a,
                outer: outer_a,
            },
            NestedRef {
                inner: inner_b,
                outer: outer_b,
            },
        )
    }
}

impl<'a, T, N> NestedRef<'a, T, N>
where
    T: ?Sized,
    N: ArrayLength<Ref<'a, ()>> + Add<B1>,
    <N as Add<B1>>::Output: ArrayLength<Ref<'a, ()>>,
    GenericArray<Ref<'a, ()>, N>:
        Lengthen<Ref<'a, ()>, Longer = GenericArray<Ref<'a, ()>, Add1<N>>>,
{
    /// Creates a shared reference to a component of the borrowed data that is contained in a nested
    /// [`RefCell`].
    ///
    /// This is an associated function, because a method would interfere with methods of the same
    /// name on the contents of the [`RefCell`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::cell::RefCell;
    /// # use nested_ref::NestedRef;
    /// let c = RefCell::new(('a', RefCell::new(2)));
    /// let b1 = NestedRef::new(c.borrow());
    /// let b2 = NestedRef::map_ref(b1, |t| t.1.borrow());
    /// assert_eq!(*b2, 2);
    /// ```
    #[inline]
    pub fn map_ref<U, F>(orig: Self, f: F) -> NestedRef<'a, U, Add1<N>>
    where
        U: ?Sized,
        F: FnOnce(&T) -> Ref<'_, U>,
    {
        // Safety: The array of outer references is kept alive as long as the returned object
        let (t, outer) = unsafe { orig.nest() };
        // Apply mapping function to obtain new inner `Ref`
        let inner = f(t);
        // Bundle all `Ref`s together
        NestedRef { inner, outer }
    }

    /// Creates an exclusive reference to a component of the borrowed data that is contained in a
    /// nested [`RefCell`].
    ///
    /// This is an associated function, because a method would interfere with methods of the same
    /// name on the contents of the [`RefCell`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::cell::RefCell;
    /// # use nested_ref::NestedRef;
    /// let c = RefCell::new(('a', RefCell::new(2)));
    /// let b1 = NestedRef::new(c.borrow());
    /// let mut b2 = NestedRef::map_ref_mut(b1, |t| t.1.borrow_mut());
    /// assert_eq!(*b2, 2);
    /// *b2 = 3;
    /// ```
    #[inline]
    pub fn map_ref_mut<U, F>(orig: Self, f: F) -> NestedRefMut<'a, U, Add1<N>>
    where
        U: ?Sized,
        F: FnOnce(&T) -> RefMut<'_, U>,
    {
        // Safety: The array of outer references is kept alive as long as the returned object
        let (t, outer) = unsafe { orig.nest() };
        // Apply mapping function to obtain new inner `RefMut`
        let inner = f(t);
        // Bundle all `Ref`s together
        NestedRefMut { inner, outer }
    }

    /// Increases the nesting level by appending the innermost reference to the outer references.
    /// Returns the innermost reference as a plain reference, along with the new array of outer
    /// references.
    ///
    /// # Safety
    ///
    /// The returned array must be kept alive as long as the returned reference.
    #[must_use]
    #[inline]
    unsafe fn nest(self) -> (&'a T, GenericArray<Ref<'a, ()>, Add1<N>>) {
        // Get a reference to the `T` that is independent of the inner `Ref`
        let t = addr_of!(*self.inner);
        // Safety: The inner `Ref` is kept alive as long as this reference, as guaranteed by the
        // caller
        let t: &'a T = unsafe { &*t };
        // Type-erase old inner `Ref` and append it to the outer `Ref`s
        let new = Ref::map(self.inner, |_| &());
        let outer = self.outer.append(new);
        // Return plain reference and array of outer references
        (t, outer)
    }
}

impl<'a, T, N> Deref for NestedRef<'a, T, N>
where
    T: ?Sized,
    N: ArrayLength<Ref<'a, ()>>,
{
    type Target = T;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

#[cfg(test)]
mod tests {
    use core::cell::{Cell, RefCell};

    use crate::NestedRef;

    /// Tests a `NestedRef` that's one level deep
    #[test]
    fn simple() {
        // Create `RefCell` and `NestedRef` into it
        let rc = RefCell::new(Cell::new(0));
        let nr = NestedRef::new(rc.borrow());
        assert_eq!(nr.get(), 0);
        assert_eq!(rc.borrow().get(), 0);
        // Mutate through `NestedRef`
        nr.set(1);
        assert_eq!(nr.get(), 1);
        assert_eq!(rc.borrow().get(), 1);
        // Mutate through independent `Ref`
        rc.borrow().set(2);
        assert_eq!(nr.get(), 2);
        assert_eq!(rc.borrow().get(), 2);
    }

    /// Tests a `NestedRef` that's three levels deep
    #[test]
    fn deep() {
        // Create `RefCell` and `NestedRef` into it
        let rc = RefCell::new(RefCell::new(RefCell::new(Cell::new(0))));
        let nr = NestedRef::new(rc.borrow());
        let nr = NestedRef::map_ref(nr, RefCell::borrow);
        let nr = NestedRef::map_ref(nr, RefCell::borrow);
        assert_eq!(nr.get(), 0);
        assert_eq!(rc.borrow().borrow().borrow().get(), 0);
        // Mutate through `NestedRef`
        nr.set(1);
        assert_eq!(nr.get(), 1);
        assert_eq!(rc.borrow().borrow().borrow().get(), 1);
        // Mutate through independent `Ref`
        rc.borrow().borrow().borrow().set(2);
        assert_eq!(nr.get(), 2);
        assert_eq!(rc.borrow().borrow().borrow().get(), 2);
    }

    /// Tests the `NestedRef::clone` method
    #[test]
    fn clone() {
        // Create `RefCell` and `NestedRef` into it
        let rc = RefCell::new(Cell::new(0));
        let nr = NestedRef::new(rc.borrow());
        assert_eq!(nr.get(), 0);
        assert_eq!(NestedRef::clone(&nr).get(), 0);
        // Mutate through `NestedRef`
        nr.set(1);
        assert_eq!(nr.get(), 1);
        assert_eq!(NestedRef::clone(&nr).get(), 1);
        // Mutate through clone
        NestedRef::clone(&nr).set(2);
        assert_eq!(nr.get(), 2);
        assert_eq!(NestedRef::clone(&nr).get(), 2);
    }

    /// Tests the `NestedRef::map` method
    #[test]
    fn map() {
        // Create `RefCell` and `NestedRef` into it
        let rc = RefCell::new((Cell::new(0), Cell::new(0)));
        let nr = NestedRef::new(rc.borrow());
        let nr = NestedRef::map(nr, |x| &x.0);
        assert_eq!(nr.get(), 0);
        assert_eq!(rc.borrow().0.get(), 0);
        // Mutate through `NestedRef`
        nr.set(1);
        assert_eq!(nr.get(), 1);
        assert_eq!(rc.borrow().0.get(), 1);
        // Mutate through independent `Ref`
        rc.borrow().0.set(2);
        assert_eq!(nr.get(), 2);
        assert_eq!(rc.borrow().0.get(), 2);
    }

    /// Tests the `NestedRef::filter_map` method
    #[test]
    fn filter_map() {
        // Create `RefCell` and `NestedRef` into it
        let rc = RefCell::new(Cell::new(0));
        let nr = NestedRef::new(rc.borrow());
        let nr = NestedRef::filter_map::<(), _>(nr, |_| None)
            .map(|_| ())
            .expect_err("This filter_map should fail");
        let nr = NestedRef::filter_map(nr, |x| Some(x))
            .map_err(|_| ())
            .expect("This filter_map should succeed");
        assert_eq!(nr.get(), 0);
        assert_eq!(rc.borrow().get(), 0);
        // Mutate through `NestedRef`
        nr.set(1);
        assert_eq!(nr.get(), 1);
        assert_eq!(rc.borrow().get(), 1);
        // Mutate through independent `Ref`
        rc.borrow().set(2);
        assert_eq!(nr.get(), 2);
        assert_eq!(rc.borrow().get(), 2);
    }

    /// Tests the `NestedRef::map_split` method
    #[test]
    fn map_split() {
        // Create `RefCell` and `NestedRef` into it
        let rc = RefCell::new((Cell::new(0), Cell::new(0)));
        let nr = NestedRef::new(rc.borrow());
        let (nr, _nr2) = NestedRef::map_split(nr, |x| (&x.0, &x.1));
        assert_eq!(nr.get(), 0);
        assert_eq!(rc.borrow().0.get(), 0);
        // Mutate through `NestedRef`
        nr.set(1);
        assert_eq!(nr.get(), 1);
        assert_eq!(rc.borrow().0.get(), 1);
        // Mutate through independent `Ref`
        rc.borrow().0.set(2);
        assert_eq!(nr.get(), 2);
        assert_eq!(rc.borrow().0.get(), 2);
    }
}
