use crate::digest::Digestible;
use serde::{Deserialize, Serialize};
use std::fmt;

pub trait Num:
    num_traits::Num
    + Ord
    + Eq
    + Clone
    + Copy
    + fmt::Debug
    + Serialize
    + for<'de> Deserialize<'de>
    + Digestible
{
}

impl<T> Num for T where
    T: num_traits::Num
        + Ord
        + Eq
        + Clone
        + Copy
        + fmt::Debug
        + Serialize
        + for<'de> Deserialize<'de>
        + Digestible
{
}
