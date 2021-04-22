#[macro_export]
macro_rules! create_id_type {
    ($name: ident) => {
        #[derive(
            Debug,
            Default,
            Copy,
            Clone,
            Eq,
            PartialEq,
            Ord,
            PartialOrd,
            Hash,
            serde::Serialize,
            serde::Deserialize,
            derive_more::Deref,
            derive_more::DerefMut,
            derive_more::Display,
            derive_more::From,
            derive_more::Into,
        )]
        pub struct $name(pub u64);

        impl $name {
            pub fn next_id() -> Self {
                use core::sync::atomic::{AtomicU64, Ordering};
                static ID_CNT: AtomicU64 = AtomicU64::new(0);
                Self(ID_CNT.fetch_add(1, Ordering::SeqCst))
            }
            pub fn unwrap(&self) -> u64 {
                match self {
                    $name(n) => *n,
                }
            }
        }
    };
}

#[cfg(test)]
mod tests {
    #[test]
    fn test_create_id() {
        create_id_type!(TestId);
        assert_eq!(TestId::next_id(), TestId(0));
        assert_eq!(TestId::next_id(), TestId(1));
        assert_eq!(TestId::next_id().unwrap(), 2);
        assert_eq!(TestId::next_id().unwrap(), 3);
        assert_eq!(TestId(2), TestId(2));
        assert_eq!(TestId::next_id(), TestId(4));
    }
}

