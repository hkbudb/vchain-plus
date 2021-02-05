
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
    //#[serde(with = "crate::acc::serde_impl")]
    //pub acc_value: ***,    // to be done
    pub child_hashes: Vec<Digest>,    // hash digests of its children
    pub child_ids: Vec<IdType>,    // TreeNode ids of its children
}

// define tree leaf node
#[derive(Debug, Clone, Eq, PartialEq, Serialize, Deserialize)]
pub struct TreeLeaf {
    pub id: IdType,
    pub block_id: BlockIdType,
    pub data_set: Vec<DataIdType>,
    //#[serde(with = "crate::acc::serde_impl")]
    //pub acc_value: ***,    // to be done
    pub obj_id: DataIdType,
    pub obj_hash: Digest,
}


// define block header
#[derive(Debug, Clone, Copy, Eq, PartialEq, Default, Serialize, Deserialize)]
pub struct BlockHeader {
    pub block_id: BlockIdType,
    pub prev_hash: Digest,
    pub ads_root: Vec<Digest>,
    pub id_root: Digest,
    pub data_set: Vec<DataIdType>
    //pub acc_val: ***    // to be done
}