use rand::Rng;

use crate::util::constraints::{
    raw_constants::{LE_ZERO, LS_INFINITY},
    ClockIndex, InnerRawInequality, RawInequality,
};

use super::{OwnedFederation, Valid, DBM};

// Based on the UDBM implementation
pub fn random_dbm_superset(dbm: DBM<Valid>) -> DBM<Valid> {
    let dim = dbm.dim;

    if dim == 1 {
        return dbm;
    }

    let mut dbm = dbm.make_dirty();

    let mut rng = rand::thread_rng();

    // Increase bounds by random amount
    for i in 0..dim {
        for j in 0..dim {
            dbm[(i, j)] = if dbm[(i, j)].is_inf() {
                LS_INFINITY
            } else {
                dbm[(i, j)].add_raw(rng.gen_range(1..20).into())
            };
        }
    }

    // Restore diagonal
    for i in 0..dim {
        dbm[(i, i)] = LE_ZERO;
    }

    // Check lower bounds
    for i in 0..dim {
        if dbm[(0, i)] > LE_ZERO {
            dbm[(0, i)] = LE_ZERO;
        }
    }

    dbm.close().unwrap()
}

// Based on the UDBM implementation
pub fn random_dbm_subset(dbm: DBM<Valid>) -> (DBM<Valid>, bool) {
    let dim = dbm.dim;
    if dim <= 1 {
        return (dbm, false);
    }

    let mut rng = rand::thread_rng();

    let mut dbm = dbm.make_dirty();

    let mut subset = false;

    for i in 0..dim {
        for j in 0..i {
            if dbm[(j, i)].is_inf() {
                if dbm[(i, j)].is_inf() {
                    dbm[(i, j)] = rng.gen_range(1..1000).into();
                    dbm = dbm.close().unwrap().make_dirty();
                    subset = true;
                } else if i != 0 || dbm[(i, j)] > LE_ZERO {
                    dbm[(i, j)] -= rng.gen_range(1..10).into();
                    if i == 0 && dbm[(i, j)] < LE_ZERO {
                        dbm[(i, j)] = LE_ZERO;
                    }
                    dbm = dbm.close().unwrap().make_dirty();
                    subset = true;
                }
            } else if dbm[(i, j)].is_inf() {
                let diff: RawInequality = rng.gen_range(2..1000).into();
                dbm[(i, j)] = diff - dbm[(j, i)];
                dbm = dbm.close().unwrap().make_dirty();
                subset = true;
            } else {
                let range: i32 = (dbm[(i, j)] + dbm[(j, i)]).into();
                if range > 2 {
                    dbm[(i, j)] = dbm[(i, j)] - 1.into() - rng.gen_range(0..range - 2).into();
                    dbm = dbm.close().unwrap().make_dirty();
                    subset = true;
                }
            }
            if subset && rng.gen_range(0..dim) == 0 {
                return (dbm.close().unwrap(), subset);
            }
        }
    }

    (dbm.close().unwrap(), subset)
}

/// Generate a random DBM with the given dimension.
// Based on the UDBM implementation
pub fn random_dbm(dim: ClockIndex) -> DBM<Valid> {
    let mut rng = rand::thread_rng();

    if dim == 1 {
        return DBM::universe(dim);
    }

    const RANGE: InnerRawInequality = 1000;
    let threshold = dim * (dim - 1) / 2;
    let mut nb_tighten = 0;
    let mut nb_thin = 0;

    let mut dbm = DBM::universe(dim).make_dirty();

    for i in 1..dim {
        let middle = rng.gen_range(0..RANGE / 2);
        dbm[(0, i)] = (1 - rng.gen_range(0..=middle)).into();
        dbm[(i, 0)] = (1 + middle + rng.gen_range(0..RANGE / 2)).into();
    }

    let mut dbm = dbm.close().unwrap();

    // Tigthen diagonals a bit
    for i in 1..dim {
        for j in 0..i {
            /* +1: to avoid division by 0
             * -1: to avoid to tighten too much (fix +1)
             */
            let rangeij: InnerRawInequality = (dbm[(i, j)] + dbm[(j, i)]).into();
            let max_tighten = if nb_tighten > threshold {
                5 * (rangeij - 1) / 12
            } else {
                7 * (rangeij - 1) / 12
            };

            let dij = rng.gen_range(0..=max_tighten);
            let dji = rng.gen_range(0..=max_tighten);

            match rng.gen_range(0..4) {
                0 => {
                    /* don't touch diagonals */
                    continue;
                }
                1 => {
                    /* tighten dbm[i,j] */
                    if dij == 0 {
                        continue;
                    }
                    let c = dbm[(i, j)] - dij.into();
                    dbm = dbm.tighten(i, j, c);
                    nb_tighten += 1;
                }
                2 => {
                    /* tighten dbm[j,i] */
                    if dji == 0 {
                        continue;
                    }

                    let c = dbm[(j, i)] - dji.into();
                    dbm = dbm.tighten(j, i, c);
                    nb_tighten += 1;
                }
                3 => {
                    let mut d_dbm = dbm.clone().make_dirty();

                    /* tighten dbm[i,j] and dbm[j,i] */
                    if dij == 0 || dji == 0 {
                        continue;
                    }

                    if rangeij - dij - dji < 2 {
                        if nb_thin < 2 {
                            let two: RawInequality = 2.into();
                            d_dbm[(i, j)] -= dij.into();
                            d_dbm[(j, i)] = two - d_dbm[(i, j)];
                            nb_thin += 1;
                        } else {
                            if rng.gen_bool(0.5) {
                                d_dbm[(i, j)] -= dij.into();
                            } else {
                                d_dbm[(j, i)] -= dji.into();
                            }
                            nb_tighten += 1;
                            break;
                        }
                    } else {
                        d_dbm[(i, j)] -= dij.into();
                        d_dbm[(j, i)] -= dji.into();
                        if i == 0 && d_dbm[(i, j)] > LE_ZERO {
                            d_dbm[(i, j)] = LE_ZERO;
                        }
                        if j == 0 && d_dbm[(j, i)] > LE_ZERO {
                            d_dbm[(j, i)] = LE_ZERO;
                        }
                    }
                    nb_tighten += 2;
                    dbm = d_dbm.close().unwrap();
                    break;
                }
                _ => unreachable!(),
            }
        }
        /* don't constrain too much */
        if nb_tighten >= 2 * threshold && rng.gen_bool(0.5) {
            break;
        }
    }

    if rng.gen_range(0..30) == 0 {
        /* deactivate a number of clocks */
        let n = rng.gen_range(0..dim - 1);
        let mut d_dbm = dbm.make_dirty();
        for _ in 0..n {
            let k = rng.gen_range(1..dim);
            d_dbm[(k, 0)] = LS_INFINITY;
            d_dbm[(0, k)] = LE_ZERO;

            for j in 1..dim {
                if j != k {
                    d_dbm[(j, k)] = LS_INFINITY; /* col to inf */
                    d_dbm[(k, j)] = LS_INFINITY; /* row to inf */
                }
            }
        }
        dbm = d_dbm.close().unwrap();
    } else if rng.gen_range(0..30) == 0 {
        dbm = dbm.up();
    }

    dbm
}

/// Get a random DBM in `fed`.
/// # Panics
/// Panics if `fed` is empty.
pub fn random_dbm_in_fed(fed: &OwnedFederation) -> DBM<Valid> {
    let mut rng = rand::thread_rng();

    let size = fed.size();
    fed.get_dbm(rng.gen_range(0..size)).unwrap()
}

/// Generate a random federation of `size` DBMs based on the DBMs in `fed`.
// Based on the UDBM implementation
pub fn random_fed_arg(fed: &OwnedFederation, size: usize) -> OwnedFederation {
    let mut rng = rand::thread_rng();
    let dim = fed.dim;

    let mut new_fed = OwnedFederation::empty(dim);
    for _ in 0..size {
        let in_fed = random_dbm_in_fed(fed);
        let new_dbm = match rng.gen_range(0..4) {
            0 => random_dbm(dim),             // Diff
            1 => in_fed,                      // Equal
            2 => random_dbm_subset(in_fed).0, // Subset
            3 => random_dbm_superset(in_fed), // Superset
            _ => unreachable!(),
        };
        new_fed.append_dbm(new_dbm);
    }

    new_fed
}

/// Generate a random `dim`-dimensional federation of `size` DBMs
/// # Panics
/// Panics if `dim == 0`.
pub fn random_fed(dim: ClockIndex, size: usize) -> OwnedFederation {
    assert!(dim > 0);
    let mut fed = OwnedFederation::empty(dim);

    for _ in 0..size {
        fed.append_dbm(random_dbm(dim));
    }

    fed
}
