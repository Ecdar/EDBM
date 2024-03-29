use std::fmt::Display;

use super::constraints::ClockIndex;

const BITS: usize = usize::BITS as usize;

const fn len_to_represent_bits(bits: usize) -> usize {
    1 + bits / BITS
    //((bits) + 31) >> 5
}

#[allow(dead_code)]
const fn len_to_represent_bytes(bytes: usize) -> usize {
    len_to_represent_bits(bytes * 8)
    //((bytes) + 3) >> 2
}

#[derive(Clone)]
pub struct BitField {
    nums: Vec<usize>,
    bit_len: usize,
}

impl BitField {
    pub fn len(&self) -> usize {
        self.bit_len
    }

    pub fn zeros(bits: usize) -> BitField {
        let len = len_to_represent_bits(bits);
        BitField {
            nums: vec![0; len],
            bit_len: bits,
        }
    }

    pub fn ones(bits: usize) -> BitField {
        let len = len_to_represent_bits(bits);
        BitField {
            nums: vec![usize::MAX; len],
            bit_len: bits,
        }
    }

    pub fn index(bit: usize) -> (usize, usize) {
        (bit / BITS, bit % BITS)
    }

    pub fn unset(&mut self, bit: usize) {
        assert!(bit < self.bit_len);
        let (index, indent) = BitField::index(bit);

        self.nums[index] &= !(1 << indent)
    }

    pub fn set(&mut self, bit: usize) {
        assert!(bit < self.bit_len);
        let (index, indent) = BitField::index(bit);
        self.nums[index] |= 1 << indent
    }

    pub fn toggle(&mut self, bit: usize) {
        assert!(bit < self.bit_len);
        let (index, indent) = BitField::index(bit);

        self.nums[index] ^= 1 << indent
    }

    pub fn get(&self, bit: usize) -> bool {
        assert!(bit < self.bit_len);
        let (index, indent) = BitField::index(bit);
        (self.nums[index] >> indent) & 1 == 1
    }

    pub fn get_b(&self, bit: usize) -> u32 {
        assert!(bit < self.bit_len);
        let (index, indent) = BitField::index(bit);
        ((self.nums[index] >> indent) & 1) as u32
    }

    pub fn get_negated_b(&self, bit: usize) -> u32 {
        1 - self.get_b(bit)
    }

    pub fn indices(&self) -> Vec<usize> {
        self.get_at_most_n_indices(self.len())
        //(0..self.bit_len).filter(|i| self.get(*i)).collect()
    }

    pub fn get_negated_and_set(&mut self, bit: usize) -> u32 {
        let b = self.get_negated_b(bit);
        self.set(bit);
        b
    }

    pub fn is_empty(&self) -> bool {
        for &i in &self.nums {
            if i != 0 {
                return false;
            }
        }

        true
    }

    pub fn get_at_most_n_indices(&self, n_cons: usize) -> Vec<usize> {
        let mut res: Vec<usize> = Vec::with_capacity(n_cons);
        let mut index = 0;
        let mut found = 0;
        for &u in &self.nums {
            if u != 0 {
                for _ in 0..BITS {
                    if self.get(index) {
                        res.push(index);
                        found += 1;

                        if found > n_cons {
                            return res;
                        }
                    }
                    index += 1;

                    if index >= self.bit_len {
                        return res;
                    }
                }
            } else {
                index += BITS;
            }
        }

        res
    }

    pub fn get_ijs(&self, dim: ClockIndex, n_cons: usize) -> Vec<(usize, usize)> {
        assert!(dim > 0);
        let mut ijs = Vec::with_capacity(n_cons);
        let mut found = 0;
        let mut i = 0usize;
        let mut j = 0usize;
        for &u in &self.nums {
            let mut b = u;
            if b != 0 {
                for _ in 0..BITS {
                    if (b & 1) == 1 {
                        while j >= dim {
                            j -= dim;
                            i += 1;
                        }
                        ijs.push((i, j));
                        found += 1;

                        if found == n_cons {
                            return ijs;
                        }
                    }
                    j += 1;
                    b >>= 1;
                }
            } else {
                j += BITS;
            }
        }

        ijs
    }

    pub fn sparse_get_ijs(&self, dim: ClockIndex, n_cons: usize) -> Vec<(usize, usize)> {
        assert!(dim > 0);
        let mut ijs = Vec::with_capacity(n_cons);
        let mut found = 0;
        let mut i = 0usize;
        let mut j = 0usize;
        for &u in &self.nums {
            let mut b = u;
            let mut visited = 0;
            while b != 0 {
                let bit_index = b.trailing_zeros() as usize;
                if bit_index != BITS - 1 {
                    b >>= bit_index + 1;
                } else {
                    b = 0;
                }

                j += bit_index;
                visited += bit_index + 1;

                while j >= dim {
                    j -= dim;
                    i += 1;
                }

                ijs.push((i, j));

                found += 1;

                if found == n_cons {
                    return ijs;
                }
                j += 1;
            }

            // add remainder
            j += BITS - visited;
        }

        ijs
    }
}

impl Display for BitField {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "BitField{{")?;

        for i in 0..self.bit_len {
            if self.get(i) {
                write!(f, "1")?
            } else {
                write!(f, "0")?
            }
        }
        write!(f, "}}")?;

        Ok(())
    }
}

#[cfg(test)]
mod test {
    use crate::util::bit_conversion::BITS;

    use super::BitField;

    #[test]
    fn bitfield() {
        let mut field = BitField::zeros(10);
        field.set(0);
        field.set(1);
        field.set(3);

        field.set(6);

        println!("{}", field);

        assert_eq!(format!("{}", field), "BitField{1101001000}");
    }

    #[test]
    fn index() {
        assert_eq!(BitField::index(BITS), (1, 0));
        assert_eq!(BitField::index(0), (0, 0));
        assert_eq!(BitField::index(1), (0, 1));
        assert_eq!(BitField::index(BITS + 1), (1, 1));
    }

    #[test]
    fn at_most() {
        let mut field = BitField::zeros(1000);
        field.set(0);
        field.set(1);
        field.set(3);

        field.set(6);

        field.set(512);

        assert_eq!(field.get_at_most_n_indices(5), &[0, 1, 3, 6, 512])
    }

    #[test]
    fn ijs() {
        let dim = 8;
        let mut field = BitField::zeros(dim * dim);
        field.set(2);
        field.set(5);
        field.set(40);
        field.set(63);

        let ijs = field.get_ijs(dim, 4);

        assert_eq!(ijs[0], (0, 2));
        assert_eq!(ijs[1], (0, 5));
        assert_eq!(ijs[2], (5, 0));
        assert_eq!(ijs[3], (7, 7));
    }

    #[test]
    fn new_ijs() {
        let dim = 8;
        let mut field = BitField::zeros(dim * dim);
        field.set(2);
        field.set(5);
        field.set(40);
        field.set(63);

        let ijs = field.sparse_get_ijs(dim, 4);

        assert_eq!(ijs[0], (0, 2));
        assert_eq!(ijs[1], (0, 5));
        assert_eq!(ijs[2], (5, 0));
        assert_eq!(ijs[3], (7, 7));
    }

    #[test]
    fn new_equals_old_ijs() {
        for size in [10, 100, 1000] {
            for dim in 1..100 {
                assert_eq!(
                    BitField::ones(size).get_ijs(dim, size),
                    BitField::ones(size).sparse_get_ijs(dim, size)
                )
            }
        }
    }

    #[test]
    fn limit_test() {
        let mut field = BitField::zeros(100);
        field.set(BITS - 1);
        assert_eq!(field.nums[0].trailing_zeros() as usize, BITS - 1);
        //assert_eq!(field.nums[0] >> 64, 0);
        assert_eq!(field.get_ijs(8, 1), field.sparse_get_ijs(8, 1))
    }
}
