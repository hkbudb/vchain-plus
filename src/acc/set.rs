use core::{
    iter::FromIterator,
    num::NonZeroU64,
    ops::{BitAnd, BitOr, Deref, DerefMut, Div},
};
use serde::{Deserialize, Serialize};
use std::collections::HashSet;

/// A set of elements.
#[derive(Debug, Default, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Set(HashSet<NonZeroU64>);

impl Set {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn with_capacity(cap: usize) -> Self {
        Self(HashSet::with_capacity(cap))
    }

    pub fn from_single_element(elm: NonZeroU64) -> Self {
        let mut set = Set::with_capacity(1);
        set.insert(elm);
        set
    }

    pub fn set_intersection(&self, rhs: &Self) -> Self {
        if self.len() < rhs.len() {
            self.iter().filter(|v| rhs.contains(v)).copied().collect()
        } else {
            rhs.iter().filter(|v| self.contains(v)).copied().collect()
        }
    }

    pub fn set_union(&self, rhs: &Self) -> Self {
        self.iter().chain(rhs.iter()).copied().collect()
    }

    pub fn set_difference(&self, rhs: &Self) -> Self {
        self.iter().filter(|v| !rhs.contains(v)).copied().collect()
    }

    pub fn is_subset_of(&self, rhs: &Self) -> bool {
        self.iter().all(|v| rhs.contains(v))
    }
}

pub fn in_place_set_intersection(lhs: Set, rhs: Set) -> Set {
    let (mut to_mutate, to_check) = if lhs.len() < rhs.len() {
        (lhs, rhs)
    } else {
        (rhs, lhs)
    };

    to_mutate.retain(|v| to_check.contains(v));
    to_mutate
}

pub fn in_place_set_union(lhs: Set, rhs: Set) -> Set {
    let (mut to_mutate, to_consume) = if lhs.len() > rhs.len() {
        (lhs, rhs)
    } else {
        (rhs, lhs)
    };

    for v in to_consume.0.into_iter() {
        to_mutate.insert(v);
    }

    to_mutate
}

pub fn in_place_set_difference(mut lhs: Set, rhs: &Set) -> Set {
    for v in rhs.iter() {
        lhs.remove(v);
    }

    lhs
}

impl Deref for Set {
    type Target = HashSet<NonZeroU64>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl DerefMut for Set {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl From<HashSet<NonZeroU64>> for Set {
    fn from(input: HashSet<NonZeroU64>) -> Self {
        Self(input)
    }
}

impl FromIterator<NonZeroU64> for Set {
    fn from_iter<T: IntoIterator<Item = NonZeroU64>>(iter: T) -> Self {
        Self(HashSet::from_iter(iter))
    }
}

impl FromIterator<u64> for Set {
    fn from_iter<T: IntoIterator<Item = u64>>(iter: T) -> Self {
        iter.into_iter()
            .map(|v| NonZeroU64::new(v).expect("set element cannot be zero."))
            .collect()
    }
}

impl BitAnd<Set> for Set {
    type Output = Set;

    fn bitand(self, rhs: Set) -> Self::Output {
        in_place_set_intersection(self, rhs)
    }
}

impl BitAnd<&'_ Set> for &'_ Set {
    type Output = Set;

    fn bitand(self, rhs: &'_ Set) -> Self::Output {
        self.set_intersection(rhs)
    }
}

impl BitOr<Set> for Set {
    type Output = Set;

    fn bitor(self, rhs: Set) -> Self::Output {
        in_place_set_union(self, rhs)
    }
}

impl BitOr<&'_ Set> for &'_ Set {
    type Output = Set;

    fn bitor(self, rhs: &'_ Set) -> Self::Output {
        self.set_union(rhs)
    }
}

impl Div<Set> for Set {
    type Output = Set;

    fn div(self, rhs: Set) -> Self::Output {
        in_place_set_difference(self, &rhs)
    }
}

impl Div<&'_ Set> for &'_ Set {
    type Output = Set;

    fn div(self, rhs: &'_ Set) -> Self::Output {
        self.set_difference(rhs)
    }
}

#[macro_export]
macro_rules! set {
    (@count) => (0);
    (@count $a:tt, $($rest:tt,)*) => (1 + set!(@count $($rest,)*));

    ($($key:expr,)+) => (set!($($key),+));
    ($($key:expr),*) => {
        {
            let _cap = set!(@count $($key,)*);
            let mut _set = $crate::acc::set::Set::with_capacity(_cap);
            $(
                let _k = core::num::NonZeroU64::new($key).expect("set element cannot be zero.");
                _set.insert(_k);
            )*
            _set
        }
    };
}

#[cfg(test)]
mod tests {
    use std::iter::FromIterator;

    use crate::acc::Set;

    #[test]
    fn test_intersection() {
        let a = set! {1, 2, 3};
        let b = set! {2, 3, 4, 5};
        let actual1 = (&a) & (&b);
        let actual2 = a & b;
        let expect = set! {2, 3};
        assert_eq!(actual1, expect);
        assert_eq!(actual2, expect);
    }

    #[test]
    fn test_union() {
        let a = set! {1, 2, 3};
        let b = set! {2, 3, 4, 5};
        let actual1 = (&a) | (&b);
        let actual2 = a | b;
        let expect = set! {1, 2, 3, 4, 5};
        assert_eq!(actual1, expect);
        assert_eq!(actual2, expect);
        let c = set! {};
        let d = set! {1};
        let e = set! {2};
        let c = &c | &d;
        let c = &c | &e;
        assert_eq!(set! {1, 2}, c);
    }

    #[test]
    fn test_difference() {
        let a = set! {1, 2, 3, 6};
        let b = set! {2, 3, 4, 5};
        let actual1 = (&a) / (&b);
        let actual2 = a / b;
        let expect = set! {1, 6};
        assert_eq!(actual1, expect);
        assert_eq!(actual2, expect);
    }

    #[test]
    fn test_is_subset_of() {
        let a = set! {1, 2, 3};
        let b = set! {2, 3, 4, 5};
        let c = set! {2, 3};
        assert!(!a.is_subset_of(&c));
        assert!(!b.is_subset_of(&c));
        assert!(!a.is_subset_of(&b));
        assert!(c.is_subset_of(&a));
        assert!(c.is_subset_of(&b));
    }

    #[test]
    fn test_from_iter() {
        let mut v = Vec::<u64>::new();
        v.push(1);
        v.push(2);
        v.push(3);
        let b = Set::from_iter(v.into_iter());
        assert_eq!(b, set! {1,2,3})
    }
}
