use std::{
    collections::{HashMap, HashSet},
    default,
    sync::{Arc, RwLock, Weak},
};

use crate::dbm::{Valid, DBM};

type HashType = u64;

#[derive(Clone)]
pub struct DBMPtr {
    arc: Arc<DBM<Valid>>,
}

impl DBMPtr {
    fn from_dbm(dbm: DBM<Valid>) -> DBMPtr {
        Self { arc: Arc::new(dbm) }
    }
    pub fn from_arc(arc: Arc<DBM<Valid>>) -> DBMPtr {
        Self { arc }
    }

    pub fn strong_count(&self) -> usize {
        Arc::strong_count(&self.arc)
    }

    pub fn weak_count(&self) -> usize {
        Arc::weak_count(&self.arc)
    }

    /// If the ptr is the only reference to the underlying DBM move it out, otherwise return a clone of it
    ///
    /// Necessary to call methods on the underlying DBM
    pub fn take_dbm(self) -> DBM<Valid> {
        match Arc::try_unwrap(self.arc) {
            Ok(dbm) => dbm,
            Err(arc) => (*arc).clone(),
        }
    }
}

impl From<Arc<DBM<Valid>>> for DBMPtr {
    fn from(arc: Arc<DBM<Valid>>) -> Self {
        Self { arc }
    }
}

pub trait DBMAllocator: Send + Sync {
    fn init() -> Arc<Self>;
    fn to_ptr(&self, dbm: DBM<Valid>) -> DBMPtr;
}

/// A thread safe DBM Allocator which tries to have equal (hash) DBMs share memory in a hash table.
///
/// The shared memory is read/updated through a RwLock ensuring thread safety but causing congestion with many writes.
pub struct SharedDBMAllocator {
    dbms: RwLock<HashMap<HashType, Weak<DBM<Valid>>>>,
}

impl DBMAllocator for SharedDBMAllocator {
    fn init() -> Arc<Self> {
        Arc::new(SharedDBMAllocator {
            dbms: RwLock::new(HashMap::default()),
        })
    }

    fn to_ptr(&self, mut dbm: DBM<Valid>) -> DBMPtr {
        let hash = dbm.hash();
        println!("Hash: {hash}");
        if let Some(res) = self.dbms.read().expect("RwLock Poisoned").get(&hash) {
            if let Some(arc) = res.upgrade() {
                return DBMPtr::from_arc(arc);
            }
        }

        let arc = Arc::new(dbm);
        self.dbms
            .write()
            .expect("RwLock Poisoned")
            .insert(hash, Arc::downgrade(&arc));
        return DBMPtr::from_arc(arc);
    }
}

/// A thread safe DBM Allocator which does not maintain internal state.
///
/// Immutable cloning of retrieved DBMs remains inexpensive due to the Arc return type
pub struct BaseDBMAllocator;

impl DBMAllocator for BaseDBMAllocator {
    fn init() -> Arc<Self> {
        Arc::new(BaseDBMAllocator)
    }

    fn to_ptr(&self, dbm: DBM<Valid>) -> DBMPtr {
        DBMPtr::from_dbm(dbm)
    }
}

mod test {
    use std::{sync::Arc, thread, time::Duration};

    use crate::{
        dbm::DBM,
        memory::allocator::{BaseDBMAllocator, SharedDBMAllocator},
    };

    use super::DBMAllocator;

    #[test]
    fn test_alloc() {
        let alloc = BaseDBMAllocator::init();
        let mut handles = vec![];

        for _ in 0..10 {
            let alloc = Arc::clone(&alloc);
            let handle = thread::spawn(move || {
                let dbm = DBM::zero(10);
                let dbm_ptr = alloc.to_ptr(dbm);

                thread::sleep(Duration::from_secs_f32(0.1));
                let ptr2 = dbm_ptr.clone();
                println!("{}", dbm_ptr.strong_count());
                let dbm = dbm_ptr.take_dbm().up();
                let dbm_ptr = alloc.to_ptr(dbm);
                println!("{}", dbm_ptr.strong_count());
            });
            handles.push(handle);
        }

        for handle in handles {
            handle.join().unwrap();
        }

        println!("Done!");
    }
}
