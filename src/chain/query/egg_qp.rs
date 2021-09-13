use crate::acc::Set;
use egg::{CostFunction, Id, Language};
use std::{
    fmt,
    hash::{Hash, Hasher},
    num::NonZeroU64,
};

#[derive(Clone, Debug, Hash, Ord, PartialOrd, Eq, PartialEq)]
pub struct SimpleQP {
    op: Operator,
    children: Vec<Id>,
    set: Option<SimpleSet>,
    cost: u32,
}

impl SimpleQP {
    pub fn new(op: Operator, children: Vec<Id>) -> Self {
        Self {
            op,
            children,
            set: None,
            cost: 0,
        }
    }
    pub fn leaf(set: SimpleSet) -> Self {
        Self {
            op: Operator::Leaf(0),
            children: vec![],
            set: Some(set),
            cost: 0,
        }
    }

    pub fn set_cost(&mut self, new_cost: u32) {
        self.cost = new_cost;
    }
}

impl Language for SimpleQP {
    fn matches(&self, other: &Self) -> bool {
        self.op == other.op && self.len() == other.len()
    }

    fn children(&self) -> &[Id] {
        &self.children
    }

    fn children_mut(&mut self) -> &mut [Id] {
        &mut self.children
    }

    fn display_op(&self) -> &dyn fmt::Display {
        panic!()
    }

    fn from_op_str(_op_str: &str, _children: Vec<Id>) -> Result<Self, String> {
        panic!()
    }
}

#[derive(Clone, Debug, Hash, Ord, PartialOrd, Eq, PartialEq)]
pub enum Operator {
    Or(u8),
    And(u8),
    Dif(u8),
    Leaf(u8),
}

#[derive(Clone, Debug, Eq)]
pub struct SimpleSet(Set);

impl Default for SimpleSet {
    fn default() -> Self {
        Self(Set::new())
    }
}

impl PartialOrd for SimpleSet {
    fn partial_cmp(&self, _other: &Self) -> Option<std::cmp::Ordering> {
        panic!()
    }
}

impl Ord for SimpleSet {
    fn cmp(&self, _other: &Self) -> std::cmp::Ordering {
        panic!()
    }
}

impl PartialEq for SimpleSet {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl Hash for SimpleSet {
    fn hash<H>(&self, state: &mut H)
    where
        H: Hasher,
    {
        let mut a: Vec<&NonZeroU64> = self.0.iter().collect();
        a.sort_unstable();
        for s in a.iter() {
            s.hash(state)
        }
    }
}

struct SimpleCostFn;
impl CostFunction<SimpleQP> for SimpleCostFn {
    type Cost = u32;
    fn cost<C>(&mut self, enode: &SimpleQP, mut costs: C) -> Self::Cost
    where
        C: FnMut(Id) -> Self::Cost,
    {
        let op_cost = enode.cost;
        enode.fold(op_cost, |sum, id| sum + costs(id))
    }
}

#[cfg(test)]
mod tests {

    #[test]
    fn test_egg() {}
}
