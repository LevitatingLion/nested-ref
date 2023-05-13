#![doc = include_str!("../README.md")]
#![no_std]
#![warn(clippy::cargo)]
#![warn(clippy::missing_docs_in_private_items)]
#![warn(clippy::pedantic)]
#![warn(clippy::undocumented_unsafe_blocks)]
#![warn(missing_docs)]
#![warn(unsafe_op_in_unsafe_fn)]

mod clone_arr;
mod exclusive;
mod shared;

#[cfg(doc)]
use core::cell::{Ref, RefCell, RefMut};

pub use exclusive::NestedRefMut;
pub use shared::NestedRef;
