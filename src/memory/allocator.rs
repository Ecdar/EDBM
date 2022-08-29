use std::{
    collections::HashMap,
    sync::{Arc, RwLock, Weak},
};

use crate::zones::{ImmutableDBM, OwnedFederation, SharedFederation, Valid, DBM};

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

impl ImmutableDBM for DBMPtr {
    #[inline(always)]
    fn as_valid_ref(&self) -> &DBM<Valid> {
        self.arc.as_ref()
    }
}

impl From<Arc<DBM<Valid>>> for DBMPtr {
    fn from(arc: Arc<DBM<Valid>>) -> Self {
        Self { arc }
    }
}

pub trait DBMAllocator: Send + Sync {
    fn to_shared_fed(&self, fed: OwnedFederation) -> SharedFederation {
        SharedFederation {
            dim: fed.dim,
            dbms: fed.dbms.into_iter().map(|dbm| self.to_ptr(dbm)).collect(),
        }
    }
    fn to_ptr(&self, dbm: DBM<Valid>) -> DBMPtr;
}

/// A thread safe DBM Allocator which tries to have equal (hash) DBMs share memory in a hash table.
///
/// The shared memory is read/updated through a RwLock ensuring thread safety but causing congestion with many writes.
pub struct SharedDBMAllocator {
    dbms: RwLock<HashMap<HashType, Weak<DBM<Valid>>>>,
}

impl SharedDBMAllocator {
    pub fn init() -> Arc<Self> {
        Arc::new(SharedDBMAllocator {
            dbms: RwLock::new(HashMap::default()),
        })
    }
}

impl DBMAllocator for SharedDBMAllocator {
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

        DBMPtr::from_arc(arc)
    }
}

/// A thread safe DBM Allocator which tries to have equal (hash) DBMs share memory in a bucket of hash tables.
///
/// The bucket approach allows for more concurrent writes.
/// The shared memory is read/updated through a RwLock ensuring thread safety but causing congestion with many writes.
pub struct BucketDBMAllocator {
    n_buckets: usize,
    buckets: Vec<RwLock<HashMap<HashType, Weak<DBM<Valid>>>>>,
}

impl BucketDBMAllocator {
    pub fn init(n_buckets: usize) -> Arc<BucketDBMAllocator> {
        Arc::new(Self {
            n_buckets,
            buckets: (0..n_buckets)
                .into_iter()
                .map(|_| RwLock::new(HashMap::default()))
                .collect(),
        })
    }
}

impl DBMAllocator for BucketDBMAllocator {
    fn to_ptr(&self, mut dbm: DBM<Valid>) -> DBMPtr {
        let hash = dbm.hash();

        let bucket = hash as usize % self.n_buckets;
        let dbms = &self.buckets[bucket];

        println!("Hash: {hash}");
        if let Some(res) = dbms.read().expect("RwLock Poisoned").get(&hash) {
            if let Some(arc) = res.upgrade() {
                return DBMPtr::from_arc(arc);
            }
        }

        let arc = Arc::new(dbm);
        dbms.write()
            .expect("RwLock Poisoned")
            .insert(hash, Arc::downgrade(&arc));

        DBMPtr::from_arc(arc)
    }
}

/// A thread safe DBM Allocator which does not maintain internal state.
///
/// Immutable cloning of retrieved DBMs remains inexpensive due to the Arc return type
pub struct BaseDBMAllocator;

impl BaseDBMAllocator {
    pub fn init() -> Arc<Self> {
        Arc::new(BaseDBMAllocator)
    }
}

impl DBMAllocator for BaseDBMAllocator {
    fn to_ptr(&self, dbm: DBM<Valid>) -> DBMPtr {
        DBMPtr::from_dbm(dbm)
    }
}

#[allow(unused)]
mod test {
    use std::{sync::Arc, thread, time::Duration};

    use crate::{
        memory::allocator::{BaseDBMAllocator, BucketDBMAllocator, SharedDBMAllocator},
        zones::{rand_gen::random_fed, ImmutableDBM, DBM},
    };

    use super::DBMAllocator;

    #[test]
    fn test_alloc() {
        let alloc = BucketDBMAllocator::init(5);
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
    }

    const TEST_ATTEMPTS: usize = 25;
    const TEST_SIZE: usize = 10;
    const DIMS: &[usize] = &[1, 2, 5];

    #[test]
    fn test_fed_alloc() {
        let mut rng = rand::thread_rng();

        for &dim in DIMS {
            for _ in 0..TEST_ATTEMPTS {
                for size in 1..TEST_SIZE {
                    let alloc = BucketDBMAllocator::init(5);
                    let mut handles = vec![];
                    for _ in 0..10 {
                        let alloc = Arc::clone(&alloc);
                        let handle = thread::spawn(move || {
                            let fed = random_fed(dim, size);
                            let shared_fed = alloc.to_shared_fed(fed.clone());

                            assert!(fed.equals(&shared_fed));

                            let fed = fed.up();
                            assert!(fed.superset_eq(&shared_fed));
                        });
                        handles.push(handle);
                    }
                }
            }
        }
    }
}
