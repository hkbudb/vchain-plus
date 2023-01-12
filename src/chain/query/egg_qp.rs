use super::{
    query_dag::DagNode,
    query_plan::{QPNode, QueryPlan},
};
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
use petgraph::{algo::toposort, graph::NodeIndex, EdgeDirection::Outgoing, Graph};
use std::{
    cmp::Ordering,
    collections::{HashSet, VecDeque},
    ops::Index,
};
use std::{
    collections::HashMap,
    fmt,
    hash::{Hash, Hasher},
    num::NonZeroU16,
    str::FromStr,
};

const EGG_NODE_LIMIT: usize = 1000;

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
        let mut a: Vec<&NonZeroU16> = self.0.iter().collect();
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
    let (expr, root_id) = create_rec_exp(dag, dag_cont)?;

    let rules: &[Rewrite<ELang, ()>] = &[
        rewrite!("rule0"; "(& ?a ?b)" => "(& ?b ?a)"),
        rewrite!("rule1"; "(| ?a ?b)" => "(| ?b ?a)"),
        rewrite!("rule2"; "(& (& ?a ?b) ?c)" => "(& ?a (& ?b ?c))"),
        rewrite!("rule3"; "(| (| ?a ?b) ?c)" => "(| ?a (| ?b ?c))"),
        rewrite!("rule4"; "(/ (| ?a ?b) ?c)" => "(| (/ ?a ?c) (/ ?b ?c))"),
        rewrite!("rule5"; "(/ ?a (& ?b ?c))" => "(| (/ ?a ?b) (/ ?a ?c))"),
        rewrite!("rule6"; "(/ (& ?a ?b) ?c)" => "(& (/ ?a ?c) (/ ?b ?c))"),
        rewrite!("rule7"; "(/ ?a (| ?b ?c))" => "(& (/ ?a ?b) (/ ?a ?c))"),
        rewrite!("rule8"; "(& (| ?a ?b) ?c)" => "(| (& ?a ?c) (& ?b ?c))"),
        rewrite!("rule9"; "(& (/ ?a ?b) ?c)" => "(/ (& ?a ?c) (& ?b ?c))"),
    ];

    let runner = Runner::default()
        .with_expr(&expr)
        .with_node_limit(EGG_NODE_LIMIT)
        .run(rules);
    let root_eclass_id = &runner.egraph.find(root_id);
    let mut extractor = Extractor::new(root_eclass_id, &runner.egraph, CostFn);
    let (_best_cost, best_expr) = extractor.find_best(runner.roots[0]);

    let new_qp = create_qp(dag, best_expr, qp)?;

    Ok(new_qp)
}

fn create_rec_exp<K: Num>(
    dag: &Graph<DagNode<K>, bool>,
    dag_cont: &HashMap<NodeIndex, QPNode<K>>,
) -> Result<(RecExpr<ELang>, Id)> {
    let mut expr = RecExpr::<ELang>::default();
    let mut idx_map = HashMap::<NodeIndex, Id>::new();

    let mut dag_inputs = match toposort(dag, None) {
        Ok(v) => v,
        Err(_) => {
            bail!("Input query plan graph not valid")
        }
    };
    let root_idx = *dag_inputs.get(0).context("empty input")?;
    let mut root_id = Id::default();
    dag_inputs.reverse();

    for idx in &dag_inputs {
        if let Some(dag_node) = dag.node_weight(*idx) {
            match dag_node {
                DagNode::Range(_) | DagNode::Keyword(_) | DagNode::BlkRt(_) => {
                    let set = dag_cont
                        .get(idx)
                        .context("Cannot find node in dag_cont when creating expr")?
                        .get_set()?
                        .clone();
                    let leaf = SimpleLeaf {
                        idx: *idx,
                        set: SimpleSet::from_set(set),
                    };
                    let leaf_idx = expr.add(ELang::Leaf(leaf));
                    if root_idx == *idx {
                        root_id = leaf_idx;
                    }
                    idx_map.insert(*idx, leaf_idx);
                }
                DagNode::Union(_) => {
                    let mut child_idxs = Vec::<NodeIndex>::new();
                    for c_idx in dag.neighbors_directed(*idx, Outgoing) {
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
                    if root_idx == *idx {
                        root_id = union_idx;
                    }
                    idx_map.insert(*idx, union_idx);
                }
                DagNode::Intersec(_) => {
                    let mut child_idxs = Vec::<NodeIndex>::new();
                    for c_idx in dag.neighbors_directed(*idx, Outgoing) {
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
                    if root_idx == *idx {
                        root_id = inter_idx;
                    }
                    idx_map.insert(*idx, inter_idx);
                }
                DagNode::Diff(_) => {
                    let mut child_idxs = Vec::<NodeIndex>::new();
                    for c_idx in dag.neighbors_directed(*idx, Outgoing) {
                        child_idxs.push(c_idx);
                    }
                    let mut qp_c_idx1 = child_idxs
                        .get(1)
                        .context("Cannot find the first qp child idx of difference")?;
                    let qp_c_idx2;
                    let edge_idx = dag
                        .find_edge(*idx, *qp_c_idx1)
                        .context("Cannot find edge")?;
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
                    if root_idx == *idx {
                        root_id = dif_idx;
                    }
                    idx_map.insert(*idx, dif_idx);
                }
            }
        }
    }

    Ok((expr, root_id))
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
                    .get(&idx)
                    .context("Cannot find node in dag_cont when create qp")?
                    .clone();

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

pub struct CostFn;
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
                let c_cost = child1_cost.sum_cost() + child2_cost.sum_cost();
                let op_cost = child1_cost.set.len() * child2_cost.set.len() * COST_COEFFICIENT;
                TestCost {
                    set,
                    c_cost,
                    op_cost,
                }
            }
            ELang::Or(n) => {
                let child1 = n[0];
                let child2 = n[1];
                let child1_cost = costs(child1);
                let child2_cost = costs(child2);
                let set = &child1_cost.set | &child2_cost.set;
                let c_cost = child1_cost.sum_cost() + child2_cost.sum_cost();
                let op_cost = child1_cost.set.len() * child2_cost.set.len() * COST_COEFFICIENT;
                TestCost {
                    set,
                    c_cost,
                    op_cost,
                }
            }
            ELang::Dif(n) => {
                let child1 = n[0];
                let child2 = n[1];
                let child1_cost = costs(child1);
                let child2_cost = costs(child2);
                let set = &child1_cost.set / &child2_cost.set;
                let c_cost = child1_cost.sum_cost() + child2_cost.sum_cost();
                let op_cost = child1_cost.set.len() * child2_cost.set.len() * COST_COEFFICIENT;
                TestCost {
                    set,
                    c_cost,
                    op_cost,
                }
            }
            ELang::Leaf(l) => {
                let s = l.set.0.clone();
                TestCost {
                    set: s,
                    c_cost: 0,
                    op_cost: 0,
                }
            }
        }
    }
}

#[derive(Clone, Debug)]
pub struct TestCost {
    set: Set,
    c_cost: usize,
    op_cost: usize,
}

impl TestCost {
    pub(crate) fn sum_cost(&self) -> usize {
        self.c_cost + self.op_cost
    }

    pub(crate) fn become_final(&mut self) {
        self.op_cost /= COST_COEFFICIENT;
    }

    pub(crate) fn reduced(&mut self) {
        self.op_cost = 0;
    }
}

impl PartialEq for TestCost {
    fn eq(&self, other: &Self) -> bool {
        self.sum_cost() == other.sum_cost()
    }
}

impl PartialOrd for TestCost {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        self.sum_cost().partial_cmp(&other.sum_cost())
    }
}

pub struct Extractor<'a, N: Analysis<ELang>> {
    cost_function: CostFn,
    costs: HashMap<Id, (TestCost, ELang)>,
    egraph: &'a EGraph<ELang, N>,
    root_eclass_id: &'a Id,
}

impl<'a, N> Extractor<'a, N>
where
    N: Analysis<ELang>,
{
    /// Create a new `Extractor` given an `EGraph` and a
    /// `CostFunction`.
    ///
    /// The extraction does all the work on creation, so this function
    /// performs the greedy search for cheapest representative of each
    /// eclass.
    pub fn new(
        root_eclass_id: &'a Id,
        egraph: &'a EGraph<ELang, N>,
        cost_function: CostFn,
    ) -> Self {
        let costs = HashMap::default();
        let mut extractor = Extractor {
            costs,
            egraph,
            cost_function,
            root_eclass_id,
        };
        extractor.find_costs();

        extractor
    }

    /// Find the cheapest (lowest cost) represented `RecExpr` in the
    /// given eclass.
    pub fn find_best(&mut self, eclass: Id) -> (TestCost, RecExpr<ELang>) {
        let mut expr = RecExpr::default();
        let (_, cost) = self.find_best_rec(&mut expr, eclass);
        (cost, expr)
    }

    fn find_best_rec(&mut self, expr: &mut RecExpr<ELang>, eclass: Id) -> (Id, TestCost) {
        let id = self.egraph.find(eclass);
        let (best_cost, best_node) = match self.costs.get(&id) {
            Some(result) => result.clone(),
            None => panic!("Failed to extract from eclass {}", id),
        };

        let node = best_node.map_children(|child| self.find_best_rec(expr, child).0);
        (expr.add(node), best_cost)
    }

    /// calculate the total cost (op_cost and c_cost) of a given node based on user_defined cost function
    fn node_total_cost(&mut self, node: &ELang) -> Option<TestCost> {
        let eg = &self.egraph;
        let has_cost = |&id| self.costs.contains_key(&eg.find(id));
        if node.children().iter().all(has_cost) {
            let costs = &self.costs;
            let cost_f = |id| costs[&eg.find(id)].0.clone();
            let mut calculated_cost = self.cost_function.cost(node, cost_f);
            let egraph = self.egraph;
            let node_eclass_id = egraph
                .lookup(node.clone())
                .unwrap_or_else(|| panic!("Can't find eclass id for this node"));

            match node {
                ELang::Or(_) => {
                    if reduced_union(egraph, *self.root_eclass_id, node_eclass_id) {
                        calculated_cost.reduced();
                    }
                }
                _ => {
                    if final_op(egraph, *self.root_eclass_id, node_eclass_id) {
                        calculated_cost.become_final();
                    }
                }
            }

            Some(calculated_cost)
        } else {
            None
        }
    }

    /// given an eclass, find its representative node with its cost(min cost)
    fn make_pass(&mut self, eclass: &EClass<ELang, N::Data>) -> Option<(TestCost, ELang)> {
        let (cost, node) = eclass
            .iter()
            .map(|n| (self.node_total_cost(n), n))
            .min_by(|a, b| cmp(&a.0, &b.0))
            .unwrap_or_else(|| panic!("Can't extract, eclass is empty: {:#?}", eclass));
        cost.map(|c| (c, node.clone()))
    }

    fn find_costs(&mut self) {
        let mut did_something = true;
        while did_something {
            did_something = false;

            for class in self.egraph.classes() {
                let pass = self.make_pass(class);
                match (self.costs.get(&class.id), pass) {
                    (None, Some(new)) => {
                        self.costs.insert(class.id, new);
                        did_something = true;
                    }
                    (Some(old), Some(new)) if new.0 < old.0 => {
                        self.costs.insert(class.id, new);
                        did_something = true;
                    }
                    _ => (),
                }
            }
        }

        for class in self.egraph.classes() {
            if !self.costs.contains_key(&class.id) {
                warn!(
                    "Failed to compute cost for eclass {}: {:?}",
                    class.id, class.nodes
                )
            }
        }
    }
}

fn cmp<T: PartialOrd>(a: &Option<T>, b: &Option<T>) -> Ordering {
    // None is high
    match (a, b) {
        (None, None) => Ordering::Equal,
        (None, Some(_)) => Ordering::Greater,
        (Some(_), None) => Ordering::Less,
        (Some(a), Some(b)) => a.partial_cmp(b).unwrap_or_else(|| panic!("")),
    }
}

/// either a top op or continuous union before it
fn final_op<N: Analysis<ELang>>(
    egraph: &EGraph<ELang, N>,
    root_eclass_id: Id,
    node_eclass_id: Id,
) -> bool {
    // i) top
    if root_eclass_id == node_eclass_id {
        return true;
    }

    // ii) continuous union before it
    let mut queue = VecDeque::<Id>::new();
    queue.push_back(root_eclass_id);

    let mut id_set = HashSet::<Id>::new();

    while let Some(id) = queue.pop_front() {
        let eclass = egraph.index(id);
        let nodes = &eclass.nodes;

        if id == node_eclass_id {
            return true;
        }

        for node in nodes {
            if let ELang::Or(children) = node {
                for c_id in children {
                    let class_id = egraph.find(*c_id);
                    if !id_set.contains(&class_id) {
                        queue.push_back(class_id);
                        id_set.insert(class_id);
                    }
                }
            }
        }
    }
    false
}

/// either a top union or continuous union
fn reduced_union<N: Analysis<ELang>>(
    egraph: &EGraph<ELang, N>,
    root_eclass_id: Id,
    node_eclass_id: Id,
) -> bool {
    // i) top
    if root_eclass_id == node_eclass_id {
        return true;
    }
    // ii) continuous union
    let mut queue = VecDeque::<Id>::new();
    queue.push_back(root_eclass_id);

    let mut id_set = HashSet::<Id>::new();
    while let Some(id) = queue.pop_front() {
        let eclass = egraph.index(id);
        let nodes = &eclass.nodes;
        let mut has_union = false;
        for node in nodes {
            if let ELang::Or(children) = node {
                has_union = true;
                for c_id in children {
                    let class_id = egraph.find(*c_id);
                    if !id_set.contains(&class_id) {
                        queue.push_back(class_id);
                        id_set.insert(class_id);
                    }
                }
            }
        }
        if id == node_eclass_id {
            return true;
        } else if !has_union {
            continue;
        }
    }
    false
}

#[cfg(test)]
mod tests {
    use super::{CostFn, ELang, Extractor, SimpleLeaf, SimpleSet};
    use crate::{chain::query::egg_qp::EGG_NODE_LIMIT, set};
    use egg::{rewrite, RecExpr, Rewrite, Runner};
    use petgraph::graph::NodeIndex;

    #[test]
    fn test_egg() {
        let rules: &[Rewrite<ELang, ()>] = &[
            rewrite!("rule0"; "(& ?a ?b)" => "(& ?b ?a)"),
            rewrite!("rule1"; "(| ?a ?b)" => "(| ?b ?a)"),
            rewrite!("rule2"; "(& (& ?a ?b) ?c)" => "(& ?a (& ?b ?c))"),
            rewrite!("rule3"; "(| (| ?a ?b) ?c)" => "(| ?a (| ?b ?c))"),
            rewrite!("rule4"; "(/ (| ?a ?b) ?c)" => "(| (/ ?a ?c) (/ ?b ?c))"),
            rewrite!("rule5"; "(/ ?a (& ?b ?c))" => "(| (/ ?a ?b) (/ ?a ?c))"),
            rewrite!("rule6"; "(/ (& ?a ?b) ?c)" => "(& (/ ?a ?c) (/ ?b ?c))"),
            rewrite!("rule7"; "(/ ?a (| ?b ?c))" => "(& (/ ?a ?b) (/ ?a ?c))"),
            rewrite!("rule8"; "(& (| ?a ?b) ?c)" => "(| (& ?a ?c) (& ?b ?c))"),
            rewrite!("rule9"; "(& (/ ?a ?b) ?c)" => "(/ (& ?a ?c) (& ?b ?c))"),
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
        let dif = expr.add(ELang::Dif([union, c]));

        let runner = Runner::default()
            .with_expr(&expr)
            .with_node_limit(EGG_NODE_LIMIT)
            .run(rules);
        let root_eclass_id = &runner.egraph.find(dif);
        let mut extractor = Extractor::new(root_eclass_id, &runner.egraph, CostFn);
        let (best_cost, _best_expr) = extractor.find_best(runner.roots[0]);
        println!("{:#?}", _best_expr);
        assert_eq!(best_cost.sum_cost(), 18);

        let leaf_b = SimpleLeaf {
            idx: NodeIndex::default(),
            set: SimpleSet(set![1, 2, 3]),
        };
        let leaf_c = SimpleLeaf {
            idx: NodeIndex::default(),
            set: SimpleSet(set![1, 4]),
        };
        let leaf_a = SimpleLeaf {
            idx: NodeIndex::default(),
            set: SimpleSet(set![1]),
        };
        let mut expr = RecExpr::default();
        let a = expr.add(ELang::Leaf(leaf_a.clone()));
        let b = expr.add(ELang::Leaf(leaf_b.clone()));
        let union1 = expr.add(ELang::Or([a, b]));
        let c = expr.add(ELang::Leaf(leaf_c.clone()));
        let union2 = expr.add(ELang::Or([union1, c]));
        let runner = Runner::default()
            .with_expr(&expr)
            .with_node_limit(EGG_NODE_LIMIT)
            .run(rules);
        let root_eclass_id = &runner.egraph.find(union2);
        let mut extractor = Extractor::new(root_eclass_id, &runner.egraph, CostFn);
        let (best_cost, _best_expr) = extractor.find_best(runner.roots[0]);
        println!("{:#?}", _best_expr);
        assert_eq!(best_cost.sum_cost(), 0);

        let leaf_a = SimpleLeaf {
            idx: NodeIndex::default(),
            set: SimpleSet(set![1]),
        };
        let leaf_b = SimpleLeaf {
            idx: NodeIndex::default(),
            set: SimpleSet(set![1, 2, 3]),
        };
        let leaf_c = SimpleLeaf {
            idx: NodeIndex::default(),
            set: SimpleSet(set![4, 5, 6]),
        };
        let mut expr = RecExpr::default();
        let a = expr.add(ELang::Leaf(leaf_a.clone()));
        let b = expr.add(ELang::Leaf(leaf_b.clone()));
        let c = expr.add(ELang::Leaf(leaf_c.clone()));
        let union = expr.add(ELang::Or([b, c]));
        let and = expr.add(ELang::And([a, union]));
        let runner = Runner::default()
            .with_expr(&expr)
            .with_node_limit(EGG_NODE_LIMIT)
            .run(rules);
        let root_eclass_id = &runner.egraph.find(and);
        let mut extractor = Extractor::new(root_eclass_id, &runner.egraph, CostFn);
        let (best_cost, _best_expr) = extractor.find_best(runner.roots[0]);
        println!("{:#?}", _best_expr);
        assert_eq!(best_cost.sum_cost(), 6);

        let leaf_a = SimpleLeaf {
            idx: NodeIndex::default(),
            set: SimpleSet(set![1, 2]),
        };
        let leaf_b = SimpleLeaf {
            idx: NodeIndex::default(),
            set: SimpleSet(set![3, 4]),
        };
        let leaf_c = SimpleLeaf {
            idx: NodeIndex::default(),
            set: SimpleSet(set![5, 6]),
        };
        let leaf_d = SimpleLeaf {
            idx: NodeIndex::default(),
            set: SimpleSet(set![7, 8]),
        };
        let mut expr = RecExpr::default();
        let a = expr.add(ELang::Leaf(leaf_a.clone()));
        let b = expr.add(ELang::Leaf(leaf_b.clone()));
        let c = expr.add(ELang::Leaf(leaf_c.clone()));
        let d = expr.add(ELang::Leaf(leaf_d.clone()));
        let union1 = expr.add(ELang::Or([b, c]));
        let union2 = expr.add(ELang::Or([union1, d]));
        let and = expr.add(ELang::And([a, union2]));
        let runner = Runner::default()
            .with_expr(&expr)
            .with_node_limit(EGG_NODE_LIMIT)
            .run(rules);
        let root_eclass_id = &runner.egraph.find(and);
        let mut extractor = Extractor::new(root_eclass_id, &runner.egraph, CostFn);
        let (best_cost, _best_expr) = extractor.find_best(runner.roots[0]);
        println!("{:#?}", _best_expr);
        assert_eq!(best_cost.sum_cost(), 12);

        let leaf_a = SimpleLeaf {
            idx: NodeIndex::default(),
            set: SimpleSet(set![1]),
        };
        let leaf_b = SimpleLeaf {
            idx: NodeIndex::default(),
            set: SimpleSet(set![1]),
        };
        let leaf_c = SimpleLeaf {
            idx: NodeIndex::default(),
            set: SimpleSet(set![2, 3]),
        };
        let leaf_d = SimpleLeaf {
            idx: NodeIndex::default(),
            set: SimpleSet(set![4, 5]),
        };
        let mut expr = RecExpr::default();
        let a = expr.add(ELang::Leaf(leaf_a.clone()));
        let b = expr.add(ELang::Leaf(leaf_b.clone()));
        let c = expr.add(ELang::Leaf(leaf_c.clone()));
        let d = expr.add(ELang::Leaf(leaf_d.clone()));
        let and1 = expr.add(ELang::And([a, b]));
        let union = expr.add(ELang::Or([c, d]));
        let _and2 = expr.add(ELang::And([and1, union]));
        let runner = Runner::default()
            .with_expr(&expr)
            .with_node_limit(EGG_NODE_LIMIT)
            .run(rules);
        let root_eclass_id = &runner.egraph.find(and);
        let mut extractor = Extractor::new(root_eclass_id, &runner.egraph, CostFn);
        let (best_cost, _best_expr) = extractor.find_best(runner.roots[0]);
        println!("{:#?}", _best_expr);
        assert_eq!(best_cost.sum_cost(), 404);

        let leaf_a = SimpleLeaf {
            idx: NodeIndex::default(),
            set: SimpleSet(set![1, 2]),
        };
        let leaf_b = SimpleLeaf {
            idx: NodeIndex::default(),
            set: SimpleSet(set![2, 3]),
        };
        let leaf_c = SimpleLeaf {
            idx: NodeIndex::default(),
            set: SimpleSet(set![2, 4]),
        };
        let leaf_d = SimpleLeaf {
            idx: NodeIndex::default(),
            set: SimpleSet(set![2, 5]),
        };
        let leaf_e = SimpleLeaf {
            idx: NodeIndex::default(),
            set: SimpleSet(set![2, 6]),
        };
        let leaf_f = SimpleLeaf {
            idx: NodeIndex::default(),
            set: SimpleSet(set![2, 7]),
        };
        let mut expr = RecExpr::default();
        let a = expr.add(ELang::Leaf(leaf_a.clone()));
        let b = expr.add(ELang::Leaf(leaf_b.clone()));
        let c = expr.add(ELang::Leaf(leaf_c.clone()));
        let d = expr.add(ELang::Leaf(leaf_d.clone()));
        let e = expr.add(ELang::Leaf(leaf_e.clone()));
        let f = expr.add(ELang::Leaf(leaf_f.clone()));
        let union1 = expr.add(ELang::Or([b, c]));
        let union2 = expr.add(ELang::Or([union1, d]));
        let union3 = expr.add(ELang::Or([union2, e]));
        let union4 = expr.add(ELang::Or([union3, f]));
        let and = expr.add(ELang::And([a, union4]));
        let runner = Runner::default()
            .with_expr(&expr)
            .with_node_limit(EGG_NODE_LIMIT)
            .run(rules);
        let root_eclass_id = &runner.egraph.find(and);
        let mut extractor = Extractor::new(root_eclass_id, &runner.egraph, CostFn);
        let (best_cost, _best_expr) = extractor.find_best(runner.roots[0]);
        println!("{:#?}", _best_expr);
        assert_eq!(best_cost.sum_cost(), 20);
    }
}
