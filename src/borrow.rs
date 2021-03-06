// Copyright 2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! A module for working with borrowed data.

use core::clone::Clone;
use core::cmp::{Eq, Ord, Ordering, PartialEq, PartialOrd};
use core::convert::AsRef;
use core::hash::{Hash, Hasher};
use core::marker::Sized;
use core::ops::Deref;
use core::option::Option;

use self::Cow::*;

pub use core::borrow::{Borrow, BorrowMut};

impl<'a, B: ?Sized> Borrow<B> for Cow<'a, B>
    where B: ToOwned,
          <B as ToOwned>::Owned: 'a
{
    fn borrow(&self) -> &B {
        &**self
    }
}

/// A generalization of `Clone` to borrowed data.
///
/// Some types make it possible to go from borrowed to owned, usually by
/// implementing the `Clone` trait. But `Clone` works only for going from `&T`
/// to `T`. The `ToOwned` trait generalizes `Clone` to construct owned data
/// from any borrow of a given type.
pub trait ToOwned {
    type Owned: Borrow<Self>;

    /// Creates owned data from borrowed data, usually by cloning.
    fn to_owned(&self) -> Self::Owned;
}

impl<T> ToOwned for T where T: Clone {
    type Owned = T;
    fn to_owned(&self) -> T {
        self.clone()
    }
}

/// A clone-on-write smart pointer.
///
/// The type `Cow` is a smart pointer providing clone-on-write functionality: it
/// can enclose and provide immutable access to borrowed data, and clone the
/// data lazily when mutation or ownership is required. The type is designed to
/// work with general borrowed data via the `Borrow` trait.
///
/// `Cow` implements `Deref`, which means that you can call
/// non-mutating methods directly on the data it encloses. If mutation
/// is desired, `to_mut` will obtain a mutable reference to an owned
/// value, cloning if necessary.
///
/// # Examples
///
/// ```
/// use std::borrow::Cow;
///
/// # #[allow(dead_code)]
/// fn abs_all(input: &mut Cow<[i32]>) {
///     for i in 0..input.len() {
///         let v = input[i];
///         if v < 0 {
///             // clones into a vector the first time (if not already owned)
///             input.to_mut()[i] = -v;
///         }
///     }
/// }
/// ```
pub enum Cow<'a, B: ?Sized + 'a>
    where B: ToOwned
{
    /// Borrowed data.
    Borrowed(&'a B),

    /// Owned data.
    Owned(
        <B as ToOwned>::Owned
    ),
}

impl<'a, B: ?Sized> Clone for Cow<'a, B> where B: ToOwned {
    fn clone(&self) -> Cow<'a, B> {
        match *self {
            Borrowed(b) => Borrowed(b),
            Owned(ref o) => {
                let b: &B = o.borrow();
                Owned(b.to_owned())
            }
        }
    }
}

impl<'a, B: ?Sized> Cow<'a, B> where B: ToOwned {
    /// Acquires a mutable reference to the owned form of the data.
    ///
    /// Clones the data if it is not already owned.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::borrow::Cow;
    ///
    /// let mut cow: Cow<[_]> = Cow::Owned(vec![1, 2, 3]);
    ///
    /// let hello = cow.to_mut();
    ///
    /// assert_eq!(hello, &[1, 2, 3]);
    /// ```
    pub fn to_mut(&mut self) -> &mut <B as ToOwned>::Owned {
        match *self {
            Borrowed(borrowed) => {
                *self = Owned(borrowed.to_owned());
                self.to_mut()
            }
            Owned(ref mut owned) => owned,
        }
    }

    /// Extracts the owned data.
    ///
    /// Clones the data if it is not already owned.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::borrow::Cow;
    ///
    /// let cow: Cow<[_]> = Cow::Owned(vec![1, 2, 3]);
    ///
    /// let hello = cow.into_owned();
    ///
    /// assert_eq!(vec![1, 2, 3], hello);
    /// ```
    pub fn into_owned(self) -> <B as ToOwned>::Owned {
        match self {
            Borrowed(borrowed) => borrowed.to_owned(),
            Owned(owned) => owned,
        }
    }
}

impl<'a, B: ?Sized> Deref for Cow<'a, B> where B: ToOwned {
    type Target = B;

    fn deref(&self) -> &B {
        match *self {
            Borrowed(borrowed) => borrowed,
            Owned(ref owned) => owned.borrow(),
        }
    }
}

impl<'a, B: ?Sized> Eq for Cow<'a, B> where B: Eq + ToOwned {}

impl<'a, B: ?Sized> Ord for Cow<'a, B> where B: Ord + ToOwned {
    #[inline]
    fn cmp(&self, other: &Cow<'a, B>) -> Ordering {
        Ord::cmp(&**self, &**other)
    }
}

impl<'a, 'b, B: ?Sized, C: ?Sized> PartialEq<Cow<'b, C>> for Cow<'a, B>
    where B: PartialEq<C> + ToOwned,
          C: ToOwned
{
    #[inline]
    fn eq(&self, other: &Cow<'b, C>) -> bool {
        PartialEq::eq(&**self, &**other)
    }
}

impl<'a, B: ?Sized> PartialOrd for Cow<'a, B> where B: PartialOrd + ToOwned {
    #[inline]
    fn partial_cmp(&self, other: &Cow<'a, B>) -> Option<Ordering> {
        PartialOrd::partial_cmp(&**self, &**other)
    }
}

impl<'a, B: ?Sized> Hash for Cow<'a, B> where B: Hash + ToOwned {
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        Hash::hash(&**self, state)
    }
}

/// Trait for moving into a `Cow`.
pub trait IntoCow<'a, B: ?Sized> where B: ToOwned {
    /// Moves `self` into `Cow`
    fn into_cow(self) -> Cow<'a, B>;
}

#[allow(deprecated)]
impl<'a, B: ?Sized> IntoCow<'a, B> for Cow<'a, B> where B: ToOwned {
    fn into_cow(self) -> Cow<'a, B> {
        self
    }
}

#[allow(deprecated)]
impl<'a, T: ?Sized + ToOwned> AsRef<T> for Cow<'a, T> {
    fn as_ref(&self) -> &T {
        self
    }
}
