use core::{
    iter::FromIterator,
    ops::{BitAnd, BitOr, Deref, DerefMut, Div},
};
use serde::{Deserialize, Serialize};
use std::collections::HashSet;

/// A set of elements.
#[derive(Debug, Default, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Set(HashSet<u64>);

impl Set {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn with_capacity(cap: usize) -> Self {
        Self(HashSet::with_capacity(cap))
    }

    pub fn set_intersection(&self, rhs: &Self) -> Self {
        self.iter().filter(|v| rhs.contains(v)).copied().collect()
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

impl Deref for Set {
    type Target = HashSet<u64>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl DerefMut for Set {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl From<HashSet<u64>> for Set {
    fn from(input: HashSet<u64>) -> Self {
        Self(input)
    }
}

impl Into<HashSet<u64>> for Set {
    fn into(self) -> HashSet<u64> {
        self.0
    }
}

impl FromIterator<u64> for Set {
    fn from_iter<T: IntoIterator<Item = u64>>(iter: T) -> Self {
        Self(HashSet::from_iter(iter))
    }
}

impl BitAnd<&'_ Set> for &'_ Set {
    type Output = Set;

    fn bitand(self, rhs: &'_ Set) -> Self::Output {
        self.set_intersection(rhs)
    }
}

impl BitOr<&'_ Set> for &'_ Set {
    type Output = Set;

    fn bitor(self, rhs: &'_ Set) -> Self::Output {
        self.set_union(rhs)
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
                _set.insert($key);
            )*
            _set
        }
    };
}

#[cfg(test)]
mod tests {
    #[test]
    fn test_intersection() {
        let a = set! {1, 2, 3};
        let b = set! {2, 3, 4, 5};
        let actual = (&a) & (&b);
        let expect = set! { 2, 3 };
        assert_eq!(actual, expect);
    }

    #[test]
    fn test_union() {
        let a = set! {1, 2, 3};
        let b = set! {2, 3, 4, 5};
        let actual = (&a) | (&b);
        let expect = set! { 1, 2, 3, 4, 5 };
        assert_eq!(actual, expect);
    }

    #[test]
    fn test_difference() {
        let a = set! {1, 2, 3, 6};
        let b = set! {2, 3, 4, 5};
        let actual = (&a) / (&b);
        let expect = set! { 1, 6 };
        assert_eq!(actual, expect);
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
}
