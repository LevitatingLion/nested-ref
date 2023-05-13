//! Exclusive reference to data contained in one or more nested [`RefCell`]s

#[cfg(doc)]
use core::cell::RefCell;
use core::{
    cell::{Ref, RefMut},
    ops::{Deref, DerefMut},
};

use generic_array::{arr, typenum::U0, ArrayLength, GenericArray};

use crate::clone_arr::clone_arr;

/// Exclusive reference to data contained in one or more nested [`RefCell`]s.
///
/// This has the same interface as [`RefMut`], and unlike [`NestedRef`](crate::NestedRef) cannot be
/// nested further.
///
/// # Examples
///
/// ```
/// # use std::cell::RefCell;
/// # use nested_ref::NestedRef;
/// // Create a `RefCell` two levels deep and a `NestedRefMut` into it
/// let rc = RefCell::new(RefCell::new(0));
/// let nr = NestedRef::new(rc.borrow());
/// let mut nr = NestedRef::map_ref_mut(nr, RefCell::borrow_mut);
///
/// // Mutate contained value
/// assert_eq!(*nr, 0);
/// *nr = 1;
/// assert_eq!(*nr, 1);
/// ```
pub struct NestedRefMut<'a, T, N>
where
    T: ?Sized,
    N: ArrayLength<Ref<'a, ()>>,
{
    /// Reference into the innermost [`RefCell`]
    pub(crate) inner: RefMut<'a, T>,
    /// Type-erased references into the other [`RefCell`]s, from outermost to innermost
    // We store a `&()` in each array entry. It would be better to store the internal `BorrowRef`
    // directly, but that's not exposed.
    pub(crate) outer: GenericArray<Ref<'a, ()>, N>,
}

impl<'a, T> NestedRefMut<'a, T, U0>
where
    T: ?Sized,
{
    /// Creates a new reference inside a single [`RefCell`]
    #[must_use]
    #[inline]
    pub fn new(inner: RefMut<'a, T>) -> Self {
        // Start with an empty array of outer `Ref`s
        let outer = arr![Ref<'a, ()>;];
        Self { inner, outer }
    }
}

impl<'a, T, N> NestedRefMut<'a, T, N>
where
    T: ?Sized,
    N: ArrayLength<Ref<'a, ()>>,
{
    /// Creates a reference to a component of the borrowed data, like [`RefMut::map`].
    ///
    /// This is an associated function, because a method would interfere with methods of the same
    /// name on the contents of the [`RefCell`].
    #[inline]
    pub fn map<U, F>(orig: Self, f: F) -> NestedRefMut<'a, U, N>
    where
        U: ?Sized,
        F: FnOnce(&mut T) -> &mut U,
    {
        // Outer `Ref` is type-erased, so just map the inner `RefMut`
        NestedRefMut {
            inner: RefMut::map(orig.inner, f),
            outer: orig.outer,
        }
    }

    /// Creates a reference to an optional component of the borrowed data, like
    /// [`RefMut::filter_map`]. The original reference is returned inside an `Err` if the closure
    /// returns `None`.
    ///
    /// This is an associated function, because a method would interfere with methods of the same
    /// name on the contents of the [`RefCell`].
    #[inline]
    #[allow(clippy::missing_errors_doc)]
    pub fn filter_map<U, F>(orig: Self, f: F) -> Result<NestedRefMut<'a, U, N>, Self>
    where
        U: ?Sized,
        F: FnOnce(&mut T) -> Option<&mut U>,
    {
        // Outer `Ref`s remain the same
        let outer = orig.outer;
        // Delegate to inner `RefMut` and put the result back together
        match RefMut::filter_map(orig.inner, f) {
            Ok(inner) => Ok(NestedRefMut { inner, outer }),
            Err(inner) => Err(NestedRefMut { inner, outer }),
        }
    }

    /// Splits a reference into multiple references for different components of the borrowed data,
    /// like [`RefMut::map_split`].
    ///
    /// This is an associated function, because a method would interfere with methods of the same
    /// name on the contents of the [`RefCell`].
    #[inline]
    pub fn map_split<U, V, F>(orig: Self, f: F) -> (NestedRefMut<'a, U, N>, NestedRefMut<'a, V, N>)
    where
        U: ?Sized,
        V: ?Sized,
        F: FnOnce(&mut T) -> (&mut U, &mut V),
    {
        // We need the outer `Ref`s two times
        let outer_a = clone_arr(&orig.outer);
        let outer_b = orig.outer;
        // Delegate to inner `RefMut` and put the results back together
        let (inner_a, inner_b) = RefMut::map_split(orig.inner, f);
        (
            NestedRefMut {
                inner: inner_a,
                outer: outer_a,
            },
            NestedRefMut {
                inner: inner_b,
                outer: outer_b,
            },
        )
    }
}

impl<'a, T, N> Deref for NestedRefMut<'a, T, N>
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

impl<'a, T, N> DerefMut for NestedRefMut<'a, T, N>
where
    T: ?Sized,
    N: ArrayLength<Ref<'a, ()>>,
{
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.inner
    }
}

#[cfg(test)]
mod tests {
    use core::cell::RefCell;

    use crate::{NestedRef, NestedRefMut};

    /// Tests a `NestedRefMut` that's one level deep
    #[test]
    fn simple() {
        // Create `RefCell` and `NestedRefMut` into it
        let rc = RefCell::new(0);
        let mut nr = NestedRefMut::new(rc.borrow_mut());

        assert_eq!(*nr, 0);
        *nr = 1;
        assert_eq!(*nr, 1);
    }

    /// Tests a `NestedRefMut` that's three levels deep
    #[test]
    fn deep() {
        // Create `RefCell` and `NestedRefMut` into it
        let rc = RefCell::new(RefCell::new(RefCell::new(0)));
        let nr = NestedRef::new(rc.borrow());
        let nr = NestedRef::map_ref(nr, RefCell::borrow);
        let mut nr = NestedRef::map_ref_mut(nr, RefCell::borrow_mut);

        assert_eq!(*nr, 0);
        *nr = 1;
        assert_eq!(*nr, 1);
    }

    /// Tests the `NestedRefMut::map` method
    #[test]
    fn map() {
        // Create `RefCell` and `NestedRefMut` into it
        let rc = RefCell::new((0, 0));
        let nr = NestedRefMut::new(rc.borrow_mut());
        let mut nr = NestedRefMut::map(nr, |x| &mut x.0);

        assert_eq!(*nr, 0);
        *nr = 1;
        assert_eq!(*nr, 1);
    }

    /// Tests the `NestedRefMut::filter_map` method
    #[test]
    fn filter_map() {
        // Create `RefCell` and `NestedRefMut` into it
        let rc = RefCell::new(0);
        let nr = NestedRefMut::new(rc.borrow_mut());
        let nr = NestedRefMut::filter_map::<(), _>(nr, |_| None)
            .map(|_| ())
            .expect_err("This filter_map should fail");
        let mut nr = NestedRefMut::filter_map(nr, |x| Some(x))
            .map_err(|_| ())
            .expect("This filter_map should succeed");

        assert_eq!(*nr, 0);
        *nr = 1;
        assert_eq!(*nr, 1);
    }

    /// Tests the `NestedRefMut::map_split` method
    #[test]
    fn map_split() {
        // Create `RefCell` and `NestedRefMut` into it
        let rc = RefCell::new((0, 0));
        let nr = NestedRefMut::new(rc.borrow_mut());
        let (mut nr, _nr2) = NestedRefMut::map_split(nr, |x| (&mut x.0, &mut x.1));

        assert_eq!(*nr, 0);
        *nr = 1;
        assert_eq!(*nr, 1);
    }
}
