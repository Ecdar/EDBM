use crate::util::{
    bit_conversion::BitField,
    constraints::raw_constants::{LE_ZERO, LS_INFINITY},
};

use super::{DBMState, DBM};

pub struct BitMatrix {
    pub bits: BitField,
    pub n_cons: u32,
}

impl BitMatrix {
    pub fn split(self) -> (BitField, u32) {
        (self.bits, self.n_cons)
    }
}

pub fn get_dbm_bit_matrix<T: DBMState>(dbm: &DBM<T>) -> BitMatrix {
    //analyze_for_min_DBM(dbm)
    clean_bit_matrix(dbm, analyze_for_min_dbm(dbm))
}

fn analyze_for_min_dbm<T: DBMState>(dbm: &DBM<T>) -> BitMatrix {
    let dim = dbm.dim;
    let mut next = vec![0usize; dim];
    let mut bits = BitField::zeros(dim * dim);

    let mut n_bcons = 0;

    let mut end = vec![];

    for i in 0..dim {
        if next[i] == 0 {
            end.push(i);

            let mut k = i;
            if i + 1 < dim {
                for j in i + 1..dim {
                    if dbm[(i, j)].bound() == -dbm[(j, i)].bound() {
                        next[k] = j;
                        k = j;
                    }
                }
            }

            next[k] = !0;
        }
    }

    for &p in &end {
        'EliminateEdges: for &q in &end {
            let bpq = dbm[(p, q)];
            if p != q && bpq < LS_INFINITY {
                for &r in &end {
                    if r != p && r != q {
                        let bqr = dbm[(p, r)];
                        let brq = dbm[(r, q)];
                        if bqr < LS_INFINITY && brq < LS_INFINITY && bpq >= bqr.add_raw(brq) {
                            continue 'EliminateEdges;
                        }
                    }
                }
                assert!(p != q);
                n_bcons += bits.get_negated_and_set(p * dim + q);
            }
        }
    }

    for &p in &end {
        let mut i = p;
        if next[i] != !0usize {
            'inner: loop {
                assert!(next[i] < dim);
                assert!(i < dim);
                n_bcons += bits.get_negated_and_set(i * dim + next[i]);
                i = next[i];

                if next[i] == !0usize {
                    break 'inner;
                }
            }
            assert!(i != p); /* not diagonal */
            n_bcons += bits.get_negated_and_set(i * dim + p)
        }
    }

    BitMatrix {
        bits,
        n_cons: n_bcons,
    }
}

fn clean_bit_matrix<T: DBMState>(dbm: &DBM<T>, bit_matrix: BitMatrix) -> BitMatrix {
    // Clocks must be positive
    let (mut bits, mut n_bcons) = bit_matrix.split();
    assert!(!bits.get(0));
    let dim = dbm.dim;
    for j in 0..dim {
        if dbm[(0, j)] >= LE_ZERO && bits.get(j) {
            bits.toggle(j);
            n_bcons -= 1;
        }
    }

    BitMatrix {
        bits,
        n_cons: n_bcons,
    }
}

#[allow(unused)]
mod test {
    use crate::zones::{minimal_graph::clean_bit_matrix, DBM};

    use super::analyze_for_min_dbm;

    #[test]
    fn test_zero() {
        let dbm = DBM::zero(5);
        let (size, bits) = analyze_for_min_dbm(&dbm).split();

        println!("DBM: {dbm}");
        println!("size: {size}");
        println!("bits: {bits}");

        //assert!(false);
    }

    #[test]
    fn test_zero_clean() {
        let dbm = DBM::zero(5);
        let bm = analyze_for_min_dbm(&dbm);
        let (bits, size) = clean_bit_matrix(&dbm, bm).split();

        println!("DBM: {dbm}");
        println!("size: {size}");
        println!("bits: {bits}");

        //assert!(false);
    }

    #[test]
    fn test_init() {
        let dbm = DBM::init(5);
        let (bits, size) = analyze_for_min_dbm(&dbm).split();

        println!("DBM: {dbm}");
        println!("size: {size}");
        println!("bits: {bits}");

        //assert!(false);
    }

    #[test]
    fn test_init_clean() {
        let dbm = DBM::init(5);
        let bm = analyze_for_min_dbm(&dbm);
        let (bits, size) = clean_bit_matrix(&dbm, bm).split();

        println!("DBM: {dbm}");
        println!("size: {size}");
        println!("bits: {bits}");

        //assert!(false);
    }
}
