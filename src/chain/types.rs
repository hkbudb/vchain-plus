use crate::digest::Digestible;
use std::fmt;

pub trait Num: num_traits::Num + Ord + Eq + Clone + Copy + fmt::Debug + Digestible {}

impl<T> Num for T where T: num_traits::Num + Ord + Eq + Clone + Copy + fmt::Debug + Digestible {}
