use super::{
    block::BlockId,
    hash::{id_tree_leaf_hash, id_tree_non_leaf_hash},
    object::{ObjId, Object},
    traits::Num,
    traits::{ReadInterface, WriteInterface},
    MAX_FANOUT,
};
use crate::{
    create_id_type,
    digest::{blake2, Digest, Digestible},
};
use anyhow::Result;
use serde::{Deserialize, Serialize};
use smallvec::SmallVec;

create_id_type!(IdTreeNodeId);
create_id_type!(IdTreeObjId);

#[derive(Debug, Clone, Eq, PartialEq, Serialize, Deserialize)]
pub enum IdTreeNode {
    Leaf(IdTreeLeafNode),
    NonLeaf(IdTreeNonLeafNode),
}

impl IdTreeNode {
    fn get_node_id(&self) -> IdTreeNodeId {
        match self {
            IdTreeNode::Leaf(n) => n.id,
            IdTreeNode::NonLeaf(n) => n.id,
        }
    }
}

impl Digestible for IdTreeNode {
    fn to_digest(&self) -> Digest {
        match self {
            IdTreeNode::Leaf(n) => n.to_digest(),
            IdTreeNode::NonLeaf(n) => n.to_digest(),
        }
    }
}

#[derive(Debug, Clone, Eq, PartialEq, Serialize, Deserialize)]
pub struct IdTreeLeafNode {
    pub id: IdTreeNodeId,
    pub obj_id: IdTreeObjId,
    pub obj_hash: Digest,
}

impl IdTreeLeafNode {
    fn new(id: IdTreeNodeId, obj_id: IdTreeObjId, obj_hash: Digest) -> Self {
        Self {
            id,
            obj_id,
            obj_hash,
        }
    }
}

impl Digestible for IdTreeLeafNode {
    fn to_digest(&self) -> Digest {
        id_tree_leaf_hash(self.obj_id, &self.obj_hash)
    }
}

#[derive(Debug, Clone, Eq, PartialEq, Serialize, Deserialize)]
pub struct IdTreeNonLeafNode {
    pub id: IdTreeNodeId,
    pub child_hashes: SmallVec<[Digest; MAX_FANOUT]>,
    pub child_ids: SmallVec<[IdTreeNodeId; MAX_FANOUT]>,
}

impl IdTreeNonLeafNode {
    fn new(
        id: IdTreeNodeId,
        child_hashes: SmallVec<[Digest; MAX_FANOUT]>,
        child_ids: SmallVec<[IdTreeNodeId; MAX_FANOUT]>,
    ) -> Self {
        Self {
            id,
            child_hashes,
            child_ids,
        }
    }
}

impl Digestible for IdTreeNonLeafNode {
    fn to_digest(&self) -> Digest {
        id_tree_non_leaf_hash(self.child_hashes.iter())
    }
}

pub fn update_id_tree(
    cur_blk_id: BlockId,
    raw_obj_ids: impl Iterator<Item = ObjId>,
    k: u64,
    chain: &mut (impl ReadInterface + WriteInterface),
) -> Result<IdTreeNode> {
    let obj_ids: Vec<IdTreeObjId> = raw_obj_ids
        .map(|o| match o {
            ObjId(t) => IdTreeObjId(t % (2 * k)),
        })
        .collect(); // get new obj ids from raw objs
    let pre_blk_id: BlockId = match cur_blk_id {
        BlockId(t) => BlockId(t - 1),
    };

    let pre_root_id: IdTreeNodeId = chain.read_block_content(pre_blk_id)?.id_tree_root_id;

    let mut id_tree_root: IdTreeNode = IdTreeNode::NonLeaf(IdTreeNonLeafNode::new(
        IdTreeNodeId::next_id(),
        SmallVec::<[Digest; MAX_FANOUT]>::new(),
        SmallVec::<[IdTreeNodeId; MAX_FANOUT]>::new(),
    )); // the root of the new id tree

    let n: u64 = obj_ids.len() as u64; // the num of obj in one block

    //let mut tmp_node_ids: Vec<IdTreeNodeId> = Vec::new(); // ids of nodes need modify
    //tmp_node_ids.push(match &id_tree_root {
    //    IdTreeNode::Leaf(n) => n.id,
    //    IdTreeNode::NonLeaf(n) => n.id,
    //});

    /* step i */
    for obj_id in obj_ids {
        let mut path: Vec<usize> = Vec::new();
        let depth: u64 = ((((n * k) as f64).log(k as f64)).ceil() + (1 as f64)) as u64;
        fanout_nary(
            match obj_id {
                IdTreeObjId(id) => id,
            },
            k,
            depth,
            &mut path,
        );

        let mut cur_node: &mut IdTreeNode = &mut id_tree_root;
        let mut index: usize = 0;

        let mut tmp_node: IdTreeNode;

        while path.len() > 1 {
            if let Some(i) = path.pop() {
                index = i;
            }

            match if let IdTreeNode::NonLeaf(n) = cur_node {
                n.child_ids.get(index)
            } else {
                None
            } {
                None => {
                    let node = IdTreeNonLeafNode::new(
                        IdTreeNodeId::next_id(),
                        SmallVec::<[Digest; MAX_FANOUT]>::new(),
                        SmallVec::<[IdTreeNodeId; MAX_FANOUT]>::new(),
                    );

                    if let IdTreeNode::NonLeaf(n) = cur_node {
                        n.child_ids[index] = node.id;
                        //tmp_node_ids.push(node.id);
                    }

                    chain.write_id_tree_node(IdTreeNode::NonLeaf(node))?;
                }
                Some(_) => {}
            }
            let mut id: IdTreeNodeId = IdTreeNodeId(0);
            if let IdTreeNode::NonLeaf(n) = cur_node {
                id = n.child_ids[index];
            }

            tmp_node = chain.read_id_tree_node(id)?;
            cur_node = &mut tmp_node;
        }

        if path.len() == 1 {
            if let Some(i) = path.pop() {
                index = i;
            }

            let node = IdTreeLeafNode::new(IdTreeNodeId::next_id(), obj_id, {
                let mut state = blake2().to_state();
                state.update(&obj_id.to_le_bytes());
                Digest::from(state.finalize())
            });

            if let IdTreeNode::NonLeaf(n) = cur_node {
                n.child_ids[index] = node.id;
                //tmp_node_ids.push(node.id);
            }

            chain.write_id_tree_node(IdTreeNode::Leaf(node))?;
        }
    }

    /* step ii and iii */
    update_id_hash(chain, id_tree_root.get_node_id(), pre_root_id);

    Ok(id_tree_root)
}

pub fn fanout_nary(obj_id: u64, fanout: u64, depth: u64, path: &mut Vec<usize>) {
    fanout_nary_inv(obj_id, fanout, depth, path);
    path.reverse();
}

fn fanout_nary_inv(
    // todo, should modify the type of each parameter as ObjId, etc
    obj_id: u64,
    fanout: u64,
    depth: u64,
    path: &mut Vec<usize>,
) {
    if depth > 0 {
        path.push((obj_id % fanout) as usize);
        fanout_nary_inv(
            (obj_id - (obj_id % fanout)) / fanout,
            fanout,
            depth - 1,
            path,
        );
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn test_fanout_nary() {
        use super::fanout_nary;
        let expect_ten: Vec<usize> = vec![1, 9, 7, 0, 3, 1];
        let expect_two: Vec<usize> = vec![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1];

        let mut v_ten: Vec<usize> = Vec::new();
        fanout_nary(197031, 10, 6, &mut v_ten);
        assert_eq!(v_ten, expect_ten);
        let mut v_two: Vec<usize> = Vec::new();
        fanout_nary(1025, 2, 11, &mut v_two);
        assert_eq!(v_two, expect_two);
    }
}

fn update_id_hash(
    chain: &mut (impl ReadInterface + WriteInterface),
    cur_id: IdTreeNodeId,
    cur_id_pre: IdTreeNodeId,
) -> Result<()> {
    // todo, question: can we return Result<> but never use it?
    let mut cur_node: &mut IdTreeNode = &mut chain.read_id_tree_node(cur_id)?;
    let cur_node_pre: &IdTreeNode = &chain.read_id_tree_node(cur_id_pre)?;
    for i in 0..MAX_FANOUT {
        match if let IdTreeNode::NonLeaf(n) = cur_node {
            n.child_ids.get(i)
        } else {
            None
        } {
            None => {
                if let (IdTreeNode::NonLeaf(n), IdTreeNode::NonLeaf(n_pre)) =
                    (&mut cur_node, &cur_node_pre)
                {
                    n.child_ids[i] = n_pre.child_ids[i];
                    n.child_hashes[i] = chain.read_id_tree_node(n_pre.child_ids[i])?.to_digest();
                }
            }
            Some(child_id) => {
                if let IdTreeNode::Leaf(_l) = chain.read_id_tree_node(*child_id)? {
                    if let IdTreeNode::NonLeaf(n) = cur_node {
                        n.child_hashes[i] = chain.read_id_tree_node(n.child_ids[i])?.to_digest();
                    }
                } else {
                    if let (IdTreeNode::NonLeaf(n), IdTreeNode::NonLeaf(n_pre)) =
                        (&mut cur_node, &cur_node_pre)
                    {
                        update_id_hash(chain, n.child_ids[i], n_pre.child_ids[i]);
                    }
                }
            }
        }
    }

    Ok(())
}
/* step ii pseudo code
call: update_id_hash(chain, new_root_id, pre_root_id);
fn update_id_hash(chain, cur_id, cur_id_pre) {
    let cur_node = &mut chain.get_node(cur_id);
    let cur_node_pre = & chain.get_node(cur_id_pre);
    for i in 0..MAX_FANOUT {
        if cur_node.child_ids[i] is None {
            cur_node.child_ids[i] = cur_node_pre.child_ids[i];
            cur_node.child_hashes[i] = chain.read_node(cur_node_pre.child_ids[i]).to_digest();
            //cur_node.child_hashes[i] = cur_node_pre.child_hashes[i];  // work if the order is paired
        } else {
            if cur_node.child_ids[i] is leaf {
                cur_node.child_hashes[i] = chain.read_node(cur_node.child_ids[i]).to_digest();
            } else {
                update_id_hash(chain, cur_node.child_ids[i], cur_node_pre.child_ids[i]);
            }
        }
    }

}
*/

// fanout_nary(objId, fanout, depth) -> vec // attention to the order direction
// given an objId, a fanout and the depth, it should return a path (list from root to leaf using mod)
// children: objId mod fanout, list size: depth

// pub fn update_ads (block_id, raw_objs, chain) // this is the signature of update_ads, not update_id_tree

/*
pub fn update_id_tree<K: Num>(
    block_id: BlockId,
    // cur_block_id,
    // *pre_block_id,
    // **start_block_id,
    // raw_obj_ids,
    // &para (time_windows as a vec of ks)  // use (max_obj_id) as k
    // chain
    raw_objs: impl Iterator<Item = Object<K>>,
    chain: &mut (impl ReadInterface + WriteInterface),
) -> Result<IdTreeNode> {  // todo error should be updated

    let param = chain.get_parameter()?;

    let obj_ids: Vec<ObjId> = raw_objs.map(|o| o.id % param.k).collect();  // moded id

    let blk_s_id = block_id - param.k;  // the id of start block
    let mut ids_removed: Vec<ObjId> = Vec::new();
    // get_obj_ids(chain, chain.read_block_content(blk_s_id).id_tree_root_id, &mut ids_removed);  // todo here the 2nd para is a result

    match chain.read_block_content(blk_s_id) {
        Ok(blk_content) => get_obj_ids(chain, blk_content.id_tree_root_id, &mut ids_removed),
        _ => (),
    };

    let pre_id_tree_root_id = chain.read_block_content(block_id-1).id_tree_root_id;
    let pre_id_tree_root = chain.read_id_tree_node(pre_id_tree_root_id);  // id_tree root is a clone of previous id tree root

    let mut id_tree_root: IdTreeNode;
    match pre_id_tree_root {
        Ok(pre_id_tree_root) => {
            id_tree_root = IdTreeNonLeafNode::new(
                IdTreeNodeId.next_id(),
                pre_id_tree_root.child_hashes.clone(),
                pre_id_tree_root.child_ids.clone(),
            );
            Ok(update(obj_ids.iter(), &chain, &id_tree_root, ids_removed))
        },
        _ => (),
    }
}

pub fn get_obj_ids(
    chain: &mut (impl ReadInterface + WriteInterface),
    id_tree_root_id: IdTreeNodeId,
    obj_ids: &mut Vec<ObjId>
) {
        match chain.read_id_tree_node(id_tree_root_id) {
            Ok(IdTreeNode::Leaf(n)) => {
                obj_ids.push(n.obj_id);
            },
            Ok(IdTreeNode::NonLeaf(n)) => {
                for child_id in n.child_ids {
                    get_obj_ids(chain, child_id, obj_ids);
                }
            },
            _ => (),
    }
}

pub fn update<'a>(
    obj_ids: impl Iterator<Item = &'a ObjId>,
    chain: &mut (impl ReadInterface + WriteInterface),
    id_tree_root: &IdTreeNode,
    ids_removed: impl Iterator<Item = &'a ObjId>
) -> &'a IdTreeNode {
    match id_tree_root {
        // ids_removed.isEmpty() => build tree use new ids then merge old tree and new tree
        // else => remove then insert
        IdTreeNode::Leaf(n) => {  // leaf, build tree directly
            let mut v_1: Vec<IdTreeNode> = Vec::new();  // stores all the new leaves with obj ids and the one in root (when root is a leaf node, it must contain a single obj)
            let mut v_2: Vec<IdTreeNode> = Vec::new();

            v_1.push(id_tree_root);
            for obj_id in obj_ids {
                v_1.push(IdTreeLeafNode::new(IdTreeNodeId.next_id(), obj_id, chain.read_object(obj_id).to_digest()));
            }

            while v_1.len() > 1 {
                loop {
                    if v_1.len() == 1 {  // left one node
                        let node = match v_1.pop() {
                            Some(n) => n,
                            None => (),
                        };
                        let mut parent_node = IdTreeNonLeafNode::new(IdTreeNodeId.next_id(), SmallVec::<[Digest; MAX_FANOUT]>::new().push(node.obj_hash), SmallVec::<[Digest; MAX_FANOUT]>::new().push(node.obj_id));
                        v_2.push(parent_node);
                        break;
                    } else if v_1.len() == 0 {
                        break;
                    }

                    let n_l = match v_1.pop() {
                        Some(n) => n,
                        None => (),
                    };
                    let n_r = match v_1.pop() {
                        Some(n) => n,
                        None => (),
                    };

                    let mut parent_node = IdTreeNonLeafNode::new(IdTreeNodeId.next_id(), SmallVec::<[Digest; MAX_FANOUT]>::new().push(n_l.obj_hash).push(n_r.obj_hash), SmallVec::<[Digest; MAX_FANOUT]>::new().push(n_l.obj_id).push(n_r.obj_id));

                    v_2.push(parent_node);
                }
                v_1.append(&mut v_2);
            }


            match v_1.pop() {
                Some(n) => &n,
                None => (),
            }
        },
        IdTreeNode::NonLeaf(n) => {

        },
    }

}

*/
