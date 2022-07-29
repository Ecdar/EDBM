use std::sync::Arc;

use crate::util::{
    bit_conversion::BitField,
    constraints::{
        raw_constants::{LS_INFINITY, ZERO},
        Bound, ClockIndex, InnerRawInequality, RawInequality,
    },
};

use super::{minimal_graph::get_DBM_bit_matrix, Valid, DBM};

struct Federation {
    dbms: Vec<Arc<DBM<Valid>>>,
}

impl Federation {
    pub fn init(dim: ClockIndex) -> Federation {
        assert!(dim > 0);

        Federation {
            dbms: vec![Arc::new(DBM::init(dim))],
        }
    }

    pub fn zero(dim: ClockIndex) -> Federation {
        assert!(dim > 0);

        Federation {
            dbms: vec![Arc::new(DBM::zero(dim))],
        }
    }
}
