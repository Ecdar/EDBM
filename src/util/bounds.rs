use super::constraints::bound_constants::INFINITY;

#[derive(Clone, Debug)]
pub struct Bounds {
    upper: Vec<Option<i32>>,
    lower: Vec<Option<i32>>,
}

impl Bounds {
    pub fn new(dim: usize) -> Self {
        assert!(dim > 0);
        let mut v = vec![None; dim];
        v[0] = Some(0);
        Bounds {
            upper: v.clone(),
            lower: v,
        }
    }

    pub fn get_dim(&self) -> usize {
        self.upper.len()
    }

    pub fn add_upper(&mut self, clock: usize, bound: i32) {
        assert!(clock > 0);
        self.upper[clock] = self.upper[clock].max(Some(bound));
    }

    pub fn add_lower(&mut self, clock: usize, bound: i32) {
        assert!(clock > 0);
        self.lower[clock] = self.lower[clock].max(Some(bound));
    }

    pub fn get_upper(&self, clock: usize) -> Option<i32> {
        self.upper[clock]
    }

    pub fn get_lower(&self, clock: usize) -> Option<i32> {
        self.lower[clock]
    }

    pub fn get_max(&self, clock: usize) -> Option<i32> {
        let l = self.get_lower(clock);
        let u = self.get_upper(clock);
        if let (Some(u), Some(l)) = (u, l) {
            Some(u.max(l))
        } else {
            u.or(l)
        }
    }

    #[allow(dead_code)]
    pub(crate) fn set_to_maxes(mut self) -> Self {
        for i in 1..self.get_dim() {
            let max = self.get_max(i);
            self.lower[i] = max;
            self.upper[i] = max;
        }

        self
    }
}
