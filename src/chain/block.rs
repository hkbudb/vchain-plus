use crate::{create_id_type, digest::{Digest, Digestible}, acc::set::Set};
use smallvec::SmallVec;
use super::{INDEX_NUM, hash::block_header_hash};
use serde::{Serialize, Deserialize};

create_id_type!(BlockId);

#[derive(Debug, Clone, Eq, PartialEq, Default, Serialize, Deserialize)]
pub struct BlockHeader {
    pub block_id: BlockId,
    pub prev_hash: Digest,
    pub id_root: Digest,
    pub ads_root: SmallVec<[Digest; INDEX_NUM]>,  // for multi-k index
    pub data_set: Set,
    // pub data_set_acc: ***
}

impl Digestible for BlockHeader{
    fn to_digest(&self) -> Digest {
        // block_header_hash(self.block_id, &self.prev_hash, &self.id_root, &ads_root.iter(), &self.data_set_acc)
        todo!()
    }
}


#[derive(Debug, Clone, Eq, PartialEq, Default, Serialize, Deserialize)]
pub struct BlockContent{
    pub block_id: BlockId,
}
