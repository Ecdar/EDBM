#[test]
fn inequality_sum() {
    use crate::util::constraints::bound_constants::INFINITY;
    use crate::util::constraints::Inequality::*;

    for i in 0..100 {
        assert!(LS(INFINITY) + LS(i) == LS(INFINITY));
        for j in 0..100 {
            assert!(LE(i) + LE(j) == LE(i + j));
            assert!(LS(i) + LE(j) == LS(i + j));
            assert!(LS(i) + LS(j) == LS(i + j));
        }
    }
}
