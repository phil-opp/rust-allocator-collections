// Copyright 2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

mod node;
mod search;
pub mod map;
pub mod set;

use allocator::Allocator;

#[doc(hidden)]
trait Recover<Q: ?Sized> {
    type Key;

    fn get<A>(&self, key: &Q, allocator: &mut A) -> Option<&Self::Key> where A: Allocator;
    fn take<A>(&mut self, key: &Q, allocator: &mut A) -> Option<Self::Key> where A: Allocator;
    fn replace<A>(&mut self, key: Self::Key, allocator: &mut A) -> Option<Self::Key> where A: Allocator;
}

/// An endpoint of a range of keys.
#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
pub enum Bound<T> {
    /// An inclusive bound.
    Included(T),
    /// An exclusive bound.
    Excluded(T),
    /// An infinite endpoint. Indicates that there is no bound in this direction.
    Unbounded,
}
