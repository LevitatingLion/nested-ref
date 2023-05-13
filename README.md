# `nested-ref`

References to data contained in one or more nested [`RefCell`]s.

When borrowing a `RefCell` that is itself contained in a `RefCell`, the `Ref`s obtained from either
`RefCell` have to be held onto. [`NestedRef`] can be used to bundle these nested `Ref`s together, to
an arbitrary level of nesting. Only the innermost reference is accessible, via the `Deref`
implementation on `NestedRef`.

The interface of `NestedRef` matches that of `Ref`, with the additional methods
[`NestedRef::map_ref`] and [`NestedRef::map_ref_mut`] to obtain a reference into a contained
`RefCell`.

For mutable references there is [`NestedRefMut`], just like `RefMut` for `Ref`. Note that only the
innermost reference is mutable, the outer references are immutable for both `NestedRef` and
`NestedRefMut`. Because of this, `NestedRefMut` cannot be nested further; to obtain a nested mutable
reference, create a `NestedRef` and use `map_ref_mut`.

This crate is `no_std` compatible and allocation-free.

## Examples

```rust
use std::cell::RefCell;

use nested_ref::NestedRef;

let rc = RefCell::new(RefCell::new(0));
let nr = NestedRef::new(rc.borrow());
let mut nr = NestedRef::map_ref_mut(nr, RefCell::borrow_mut);
assert_eq!(*nr, 0);
*nr = 1;
```

Suppose you have a data structure contained in a `RefCell`, where each entry is also contained in a
`RefCell`. `NestedRef` allows you to return a reference to the inner data, while holding onto the
`Ref`s obtained from both `RefCell`s.

```rust
use std::cell::RefCell;

use generic_array::typenum::U1;
use nested_ref::{NestedRef, NestedRefMut};

struct MyVec<T> {
    inner: RefCell<Vec<RefCell<T>>>,
}

impl<T> MyVec<T> {
    fn get(&self, idx: usize) -> NestedRef<'_, T, U1> {
        let nr = NestedRef::new(self.inner.borrow());
        NestedRef::map_ref(nr, |r| r[idx].borrow())
    }

    fn get_mut(&self, idx: usize) -> NestedRefMut<'_, T, U1> {
        let nr = NestedRef::new(self.inner.borrow());
        NestedRef::map_ref_mut(nr, |r| r[idx].borrow_mut())
    }
}
```

## License

Licensed under either of [MIT License](LICENSE-MIT) or [Apache License, Version 2.0](LICENSE-APACHE)
at your option.

Unless you explicitly state otherwise, any contribution intentionally submitted for inclusion in
this crate by you, as defined in the Apache-2.0 license, shall be dual licensed as above, without
any additional terms or conditions.
