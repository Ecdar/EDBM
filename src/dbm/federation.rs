use std::sync::Arc;

use crate::{
    memory::allocator::DBMPtr,
    util::{
        bit_conversion::BitField,
        constraints::{
            raw_constants::{LS_INFINITY, ZERO},
            Bound, ClockIndex, InnerRawInequality, RawInequality,
        },
    },
};

use super::{minimal_graph::get_DBM_bit_matrix, Valid, DBM};

struct Federation {
    dbms: Vec<DBMPtr>,
}

impl Federation {
    pub fn init(dim: ClockIndex) -> Federation {
        assert!(dim > 0);

        Federation {
            dbms: todo!(), // vec![Arc::new(DBM::init(dim))],
        }
    }

    pub fn zero(dim: ClockIndex) -> Federation {
        assert!(dim > 0);

        Federation {
            dbms: todo!(), //vec![Arc::new(DBM::zero(dim))],
        }
    }
}
