use std::collections::HashSet;

use crate::dbm::{Valid, DBM};

pub struct DBMAllocator {
    dbms: HashSet<DBM<Valid>>,
}
