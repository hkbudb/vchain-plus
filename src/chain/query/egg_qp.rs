use crate::{
    acc::Set,
    chain::{
        query::{
            query_dag::{DiffNode, IntersecNode, UnionNode},
            query_plan::{QPDiff, QPIntersec, QPUnion},
        },
        traits::Num,
        COST_COEFFICIENT,
    },
};
use anyhow::{bail, Context, Result};
use egg::*;
use howlong::Duration;
use petgraph::{algo::toposort, graph::NodeIndex, EdgeDirection::Outgoing, Graph};
use std::{
    collections::HashMap,
    fmt,
    hash::{Hash, Hasher},
    num::NonZeroU64,
    str::FromStr,
};

use super::{
    query_dag::DagNode,
    query_plan::{QPNode, QueryPlan},
};

#[derive(Clone, Debug, Eq)]
pub struct SimpleSet(Set);

impl Default for SimpleSet {
    fn default() -> Self {
        Self(Set::new())
    }
}

impl SimpleSet {
    fn from_set(s: Set) -> Self {
        Self(s)
    }
}

impl PartialOrd for SimpleSet {
    fn partial_cmp(&self, _other: &Self) -> Option<std::cmp::Ordering> {
        panic!("should not reach here");
    }
}

impl Ord for SimpleSet {
    fn cmp(&self, _other: &Self) -> std::cmp::Ordering {
        panic!("should not reach here");
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

#[derive(Clone, Debug, Hash, Ord, PartialOrd, Eq, PartialEq)]
pub struct SimpleLeaf {
    idx: NodeIndex,
    set: SimpleSet,
}

impl SimpleLeaf {
    fn get_idx(&self) -> NodeIndex {
        self.idx
    }
}

impl fmt::Display for SimpleLeaf {
    fn fmt(&self, _f: &mut fmt::Formatter<'_>) -> fmt::Result {
        panic!("should not reach here");
    }
}

impl FromStr for SimpleLeaf {
    type Err = String;

    fn from_str(_s: &str) -> Result<Self, Self::Err> {
        panic!("should not reach here");
    }
}

define_language! {
    pub enum ELang {
        "&" = And([Id; 2]),
        "|" = Or([Id; 2]),
        "/" = Dif([Id; 2]),
        Leaf(SimpleLeaf),
    }
}

pub fn egg_optimize<K: Num>(
    dag: &Graph<DagNode<K>, bool>,
    qp: &mut QueryPlan<K>,
) -> Result<Graph<DagNode<K>, bool>> {
    let dag_cont = qp.get_dag_cont();
    let expr = create_rec_exp(dag, dag_cont)?;

    let rules: &[Rewrite<ELang, ()>] = &[
        rewrite!("rule1"; "(/ (| ?a ?b) ?c)" => "(| (/ ?a ?c) (/ ?b ?c))"),
        rewrite!("rule2"; "(/ ?a (& ?b ?c))" => "(| (/ ?a ?b) (/ ?a ?c))"),
        rewrite!("rule3"; "(/ (& ?a ?b) ?c)" => "(& (/ ?a ?c) (/ ?b ?c))"),
        rewrite!("rule4"; "(/ ?a (| ?b ?c))" => "(& (/ ?a ?b) (/ ?a ?c))"),
        rewrite!("rule5"; "(& (| ?a ?b) ?c)" => "(| (& ?a ?c) (& ?b ?c))"),
        rewrite!("rule6"; "(& (/ ?a ?b) ?c)" => "(/ (& ?a ?c) (& ?b ?c))"),
        // rewrite!("rule7"; "(& (& ?a ?b) ?c)" => "(& (& ?a ?c) ?b)"),
        // rewrite!("rule8"; "(& (& ?a ?b) ?c)" => "(& (& ?b ?c) ?a)"),
        // rewrite!("rule9"; "(| (| ?a ?b) ?c)" => "(| (| ?a ?c) ?b)"),
        // rewrite!("rule10"; "(| (| ?a ?b) ?c)" => "(| (| ?b ?c) ?a)"),
    ];

    let runner = Runner::default()
        .with_expr(&expr)
        .with_time_limit(Duration::new(2, 0))
        .run(rules);
    let mut extractor = Extractor::new(&runner.egraph, CostFn);
    let (_best_cost, best_expr) = extractor.find_best(runner.roots[0]);

    let new_qp = create_qp(dag, best_expr, qp)?;

    Ok(new_qp)
}

fn create_rec_exp<K: Num>(
    dag: &Graph<DagNode<K>, bool>,
    dag_cont: &HashMap<NodeIndex, QPNode<K>>,
) -> Result<RecExpr<ELang>> {
    let mut expr = RecExpr::<ELang>::default();
    let mut idx_map = HashMap::<NodeIndex, Id>::new();

    let mut dag_inputs = match toposort(dag, None) {
        Ok(v) => v,
        Err(_) => {
            bail!("Input query plan graph not valid")
        }
    };
    dag_inputs.reverse();

    for idx in dag_inputs {
        if let Some(dag_node) = dag.node_weight(idx) {
            match dag_node {
                DagNode::Range(_) | DagNode::Keyword(_) | DagNode::BlkRt(_) => {
                    let set = dag_cont
                        .get(&idx)
                        .context("Cannot find node in dag_cont")?
                        .get_set()?
                        .clone();
                    let leaf = SimpleLeaf {
                        idx,
                        set: SimpleSet::from_set(set),
                    };
                    let leaf_idx = expr.add(ELang::Leaf(leaf));
                    idx_map.insert(idx, leaf_idx);
                }
                DagNode::Union(_) => {
                    let mut child_idxs = Vec::<NodeIndex>::new();
                    for c_idx in dag.neighbors_directed(idx, Outgoing) {
                        child_idxs.push(c_idx);
                    }
                    let qp_c_idx1 = child_idxs
                        .get(0)
                        .context("Cannot find the first child idx of union")?;
                    let exp_c_idx1 = idx_map
                        .get(qp_c_idx1)
                        .context("Cannot find id in idx_map")?;
                    let qp_c_idx2 = child_idxs
                        .get(1)
                        .context("Cannot find the second qp child idx of union")?;
                    let exp_c_idx2 = idx_map
                        .get(qp_c_idx2)
                        .context("Cannot find id in idx_map")?;
                    let union_idx = expr.add(ELang::Or([*exp_c_idx1, *exp_c_idx2]));
                    idx_map.insert(idx, union_idx);
                }
                DagNode::Intersec(_) => {
                    let mut child_idxs = Vec::<NodeIndex>::new();
                    for c_idx in dag.neighbors_directed(idx, Outgoing) {
                        child_idxs.push(c_idx);
                    }
                    let qp_c_idx1 = child_idxs
                        .get(0)
                        .context("Cannot find the first child idx of union")?;
                    let exp_c_idx1 = idx_map
                        .get(qp_c_idx1)
                        .context("Cannot find id in idx_map")?;
                    let qp_c_idx2 = child_idxs
                        .get(1)
                        .context("Cannot find the second qp child idx of union")?;
                    let exp_c_idx2 = idx_map
                        .get(qp_c_idx2)
                        .context("Cannot find id in idx_map")?;
                    let inter_idx = expr.add(ELang::And([*exp_c_idx1, *exp_c_idx2]));
                    idx_map.insert(idx, inter_idx);
                }
                DagNode::Diff(_) => {
                    let mut child_idxs = Vec::<NodeIndex>::new();
                    for c_idx in dag.neighbors_directed(idx, Outgoing) {
                        child_idxs.push(c_idx);
                    }
                    let mut qp_c_idx1 = child_idxs
                        .get(1)
                        .context("Cannot find the first qp child idx of difference")?;
                    let qp_c_idx2;
                    let edge_idx = dag.find_edge(idx, *qp_c_idx1).context("Cannot find edge")?;
                    let weight = dag.edge_weight(edge_idx).context("Cannot find edge")?;
                    if !*weight {
                        qp_c_idx2 = child_idxs
                            .get(0)
                            .context("Cannot find the first qp child idx of difference")?;
                    } else {
                        qp_c_idx1 = child_idxs
                            .get(0)
                            .context("Cannot find the first qp child idx of difference")?;
                        qp_c_idx2 = child_idxs
                            .get(1)
                            .context("Cannot find the first qp child idx of difference")?;
                    }
                    let exp_c_idx1 = idx_map
                        .get(qp_c_idx1)
                        .context("Cannot find id in idx_map")?;
                    let exp_c_idx2 = idx_map
                        .get(qp_c_idx2)
                        .context("Cannot find id in idx_map")?;
                    let dif_idx = expr.add(ELang::Dif([*exp_c_idx1, *exp_c_idx2]));
                    idx_map.insert(idx, dif_idx);
                }
            }
        }
    }

    Ok(expr)
}

fn create_qp<K: Num>(
    old_dag: &Graph<DagNode<K>, bool>,
    expr: RecExpr<ELang>,
    qp: &mut QueryPlan<K>,
) -> Result<Graph<DagNode<K>, bool>> {
    let mut new_dag = Graph::<DagNode<K>, bool>::new();
    let dag_cont = qp.get_dag_cont_mut();
    let mut new_dag_cont = HashMap::<NodeIndex, QPNode<K>>::new();
    let mut idx_map = HashMap::<Id, NodeIndex>::new();

    let nodes = expr.as_ref();
    let nodes_len = nodes.len();
    let mut root_idx = NodeIndex::default();
    for (pos, node) in nodes.iter().enumerate() {
        match node {
            ELang::And(children) => {
                let new_idx = new_dag.add_node(DagNode::Intersec(IntersecNode {}));
                let c1 = children[0];
                let c2 = children[1];
                let c1_idx = idx_map.get(&c1).context("Cannot get c1 idx in idx map")?;
                let c2_idx = idx_map.get(&c2).context("Cannot get c2 idx in idx map")?;
                new_dag.add_edge(new_idx, *c1_idx, false);
                new_dag.add_edge(new_idx, *c2_idx, true);
                let c1_n = new_dag_cont
                    .get(c1_idx)
                    .context("node does not exist in new dag_cont")?;
                let set1 = c1_n.get_set()?;
                let c2_n = new_dag_cont
                    .get(c2_idx)
                    .context("node does not exist in new dag_cont")?;
                let set2 = c2_n.get_set()?;
                let set = set1 & set2;
                let intersec_node = QPIntersec { set: Some(set) };
                new_dag_cont.insert(new_idx, QPNode::Intersec(intersec_node));
                idx_map.insert(Id::from(pos), new_idx);
                if pos + 1 == nodes_len {
                    root_idx = new_idx;
                }
            }
            ELang::Or(children) => {
                let new_idx = new_dag.add_node(DagNode::Union(UnionNode {}));
                let c1 = children[0];
                let c2 = children[1];
                let c1_idx = idx_map.get(&c1).context("Cannot get c1 idx in idx map")?;
                let c2_idx = idx_map.get(&c2).context("Cannot get c2 idx in idx map")?;
                new_dag.add_edge(new_idx, *c1_idx, false);
                new_dag.add_edge(new_idx, *c2_idx, true);
                let c1_n = new_dag_cont
                    .get(c1_idx)
                    .context("node does not exist in new dag_cont")?;
                let set1 = c1_n.get_set()?;
                let c2_n = new_dag_cont
                    .get(c2_idx)
                    .context("node does not exist in new dag_cont")?;
                let set2 = c2_n.get_set()?;
                let set = set1 | set2;
                let union_node = QPUnion { set: Some(set) };
                new_dag_cont.insert(new_idx, QPNode::Union(union_node));
                idx_map.insert(Id::from(pos), new_idx);
                if pos + 1 == nodes_len {
                    root_idx = new_idx;
                }
            }
            ELang::Dif(children) => {
                let new_idx = new_dag.add_node(DagNode::Diff(DiffNode {}));
                let c1 = children[0];
                let c2 = children[1];
                let c1_idx = idx_map.get(&c1).context("Cannot get c1 idx in idx map")?;
                let c2_idx = idx_map.get(&c2).context("Cannot get c2 idx in idx map")?;
                new_dag.add_edge(new_idx, *c1_idx, false);
                new_dag.add_edge(new_idx, *c2_idx, true);
                let c1_n = new_dag_cont
                    .get(c1_idx)
                    .context("node does not exist in new dag_cont")?;
                let set1 = c1_n.get_set()?;
                let c2_n = new_dag_cont
                    .get(c2_idx)
                    .context("node does not exist in new dag_cont")?;
                let set2 = c2_n.get_set()?;
                let set = set1 / set2;
                let diff_node = QPDiff { set: Some(set) };
                new_dag_cont.insert(new_idx, QPNode::Diff(diff_node));
                idx_map.insert(Id::from(pos), new_idx);
                if pos + 1 == nodes_len {
                    root_idx = new_idx;
                }
            }
            ELang::Leaf(n) => {
                let idx = n.get_idx();
                let qp_node = dag_cont
                    .remove(&idx)
                    .context("Cannot find node in dag_cont")?;

                let dag_n = old_dag
                    .node_weight(idx)
                    .context("Idx not exist in old dag")?;
                let new_idx = new_dag.add_node(dag_n.clone());
                new_dag_cont.insert(new_idx, qp_node);
                idx_map.insert(Id::from(pos), new_idx);
                if pos + 1 == nodes_len {
                    root_idx = new_idx;
                }
            }
        }
    }

    qp.update_dag_cont(new_dag_cont);
    qp.update_root_idx(root_idx);

    Ok(new_dag)
}

struct CostFn;
impl CostFunction<ELang> for CostFn {
    type Cost = TestCost;
    fn cost<C>(&mut self, enode: &ELang, mut costs: C) -> Self::Cost
    where
        C: FnMut(Id) -> Self::Cost,
    {
        //costs: a function(hashmap in fact) which can know the cost of given id
        match enode {
            ELang::And(n) => {
                let child1 = n[0];
                let child2 = n[1];
                let child1_cost = costs(child1);
                let child2_cost = costs(child2);
                let set = &child1_cost.set & &child2_cost.set;
                let cost = child1_cost.set.len() * child2_cost.set.len() * COST_COEFFICIENT
                    + child1_cost.cost
                    + child2_cost.cost;
                TestCost { set, cost }
            }
            ELang::Or(n) => {
                let child1 = n[0];
                let child2 = n[1];
                let child1_cost = costs(child1);
                let child2_cost = costs(child2);
                let set = &child1_cost.set | &child2_cost.set;
                let cost = child1_cost.set.len() * child2_cost.set.len() * COST_COEFFICIENT
                    + child1_cost.cost
                    + child2_cost.cost;
                TestCost { set, cost }
            }
            ELang::Dif(n) => {
                let child1 = n[0];
                let child2 = n[1];
                let child1_cost = costs(child1);
                let child2_cost = costs(child2);
                let set = &child1_cost.set / &child2_cost.set;
                let cost = child1_cost.set.len() * child2_cost.set.len() * COST_COEFFICIENT
                    + child1_cost.cost
                    + child2_cost.cost;
                TestCost { set, cost }
            }
            ELang::Leaf(l) => {
                let c = 0;
                let s = l.set.0.clone();
                TestCost { set: s, cost: c }
            }
        }
    }
}

#[derive(Clone, Debug)]
pub struct TestCost {
    set: Set,
    cost: usize,
}

impl PartialEq for TestCost {
    fn eq(&self, other: &Self) -> bool {
        self.cost == other.cost
    }
}

impl PartialOrd for TestCost {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        self.cost.partial_cmp(&other.cost)
    }
}

#[cfg(test)]
mod tests {
    use super::{CostFn, ELang, SimpleLeaf, SimpleSet};
    use crate::set;
    use egg::*;
    use petgraph::graph::NodeIndex;

    #[test]
    fn test_egg() {
        let rules: &[Rewrite<ELang, ()>] = &[
            rewrite!("rule1"; "(/ (| ?a ?b) ?c)" => "(| (/ ?a ?c) (/ ?b ?c))"),
            rewrite!("rule2"; "(/ ?a (& ?b ?c))" => "(| (/ ?a ?b) (/ ?a ?c))"),
            rewrite!("rule3"; "(/ (& ?a ?b) ?c)" => "(& (/ ?a ?c) (/ ?b ?c))"),
            rewrite!("rule4"; "(/ ?a (| ?b ?c))" => "(& (/ ?a ?b) (/ ?a ?c))"),
            rewrite!("rule5"; "(& (| ?a ?b) ?c)" => "(| (& ?a ?c) (& ?b ?c))"),
            rewrite!("rule6"; "(& (/ ?a ?b) ?c)" => "(/ (& ?a ?c) (& ?b ?c))"),
            rewrite!("rule7"; "(& (& ?a ?b) ?c)" => "(& (& ?a ?c) ?b)"),
            rewrite!("rule8"; "(& (& ?a ?b) ?c)" => "(& (& ?b ?c) ?a)"),
            rewrite!("rule9"; "(| (| ?a ?b) ?c)" => "(| (| ?a ?c) ?b)"),
            rewrite!("rule10"; "(| (| ?a ?b) ?c)" => "(| (| ?b ?c) ?a)"),
        ];
        let leaf_a = SimpleLeaf {
            idx: NodeIndex::default(),
            set: SimpleSet(set![1, 2, 3]),
        };
        let leaf_b = SimpleLeaf {
            idx: NodeIndex::default(),
            set: SimpleSet(set![1, 2, 4]),
        };
        let leaf_c = SimpleLeaf {
            idx: NodeIndex::default(),
            set: SimpleSet(set![1, 2, 5]),
        };

        let mut expr = RecExpr::default();
        let a = expr.add(ELang::Leaf(leaf_a.clone()));
        let b = expr.add(ELang::Leaf(leaf_b.clone()));
        let union = expr.add(ELang::Or([a, b]));
        let c = expr.add(ELang::Leaf(leaf_c.clone()));
        let _dif = expr.add(ELang::Dif([union, c]));

        let runner = Runner::default().with_expr(&expr).run(rules);
        let mut extractor = Extractor::new(&runner.egraph, CostFn);
        let (best_cost, _best_expr) = extractor.find_best(runner.roots[0]);
        assert_eq!(best_cost.cost, 3800);

        let leaf_a = SimpleLeaf {
            idx: NodeIndex::default(),
            set: SimpleSet(set![1, 2, 3]),
        };
        let leaf_b = SimpleLeaf {
            idx: NodeIndex::default(),
            set: SimpleSet(set![1, 4]),
        };
        let leaf_c = SimpleLeaf {
            idx: NodeIndex::default(),
            set: SimpleSet(set![1]),
        };
        let mut expr = RecExpr::default();
        let a = expr.add(ELang::Leaf(leaf_a.clone()));
        let b = expr.add(ELang::Leaf(leaf_b.clone()));
        let union1 = expr.add(ELang::Or([a, b]));
        let c = expr.add(ELang::Leaf(leaf_c.clone()));
        let _union2 = expr.add(ELang::Or([union1, c]));
        let runner = Runner::default().with_expr(&expr).run(rules);
        let mut extractor = Extractor::new(&runner.egraph, CostFn);
        let (best_cost, _best_expr) = extractor.find_best(runner.roots[0]);
        assert_eq!(best_cost.cost, 1600);
    }
}
