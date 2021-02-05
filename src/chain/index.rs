
// define tree node
#[derive(Debug, Clone, Eq, PartialEq, Serialize, Deserialize)]
pub enum TreeNode {
    NonLeaf(Box<TreeNonLeaf>),
    Leaf(Box<TreeLeaf>),
}

//create_id_type!(IdType);    // for TreeNode id
//create_id_type!(BlockIdType);    // for Block id
//create_id_type!(DataIdType);    // for Data id

// define tree non-leaf node
#[derive(Debug, Clone, Eq, PartialEq, Serialize, Deserialize)]
pub struct TreeNonLeaf {
    pub id: IdType,
    pub block_id: BlockIdType,
    pub data_set: Vec<DataIdType>,
    #[serde(with = "crate::acc::serde_impl")]
    //pub acc_value: ***,    // to be done
    pub hash_digest: Digest,    // hash digest of this non-leaf node
    pub child_hashes: Vec<Digest>,    // hash digests of its children
    pub child_ids: Vec<IdType>,
}