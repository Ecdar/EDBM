use std::{fmt::Display, slice::Iter};

use super::constraints::ClockIndex;

pub const fn u32s_to_represent_bits(bits: usize) -> usize {
    ((bits) + 31) >> 5
}

pub const fn u32s_to_represent_bytes(bytes: usize) -> usize {
    ((bytes) + 3) >> 2
}

#[derive(Clone)]
pub struct BitField {
    u32s: Vec<u32>,
    bit_len: usize,
}

impl BitField {
    pub fn len(&self) -> usize {
        self.bit_len
    }

    pub fn zeros(bits: usize) -> BitField {
        let len = u32s_to_represent_bits(bits);
        BitField {
            u32s: vec![0; len],
            bit_len: bits,
        }
    }

    pub fn ones(bits: usize) -> BitField {
        let len = u32s_to_represent_bits(bits);
        BitField {
            u32s: vec![u32::MAX; len],
            bit_len: bits,
        }
    }

    pub fn index(bit: usize) -> (usize, usize) {
        /*if bit == 0 {
            return (0, 0);
        }
        let u32s = u32s_to_represent_bits(bit);*/

        (bit / 32, bit % 32)
    }

    pub fn unset(&mut self, bit: usize) {
        assert!(bit < self.bit_len);
        let (index, indent) = BitField::index(bit);

        self.u32s[index] &= !(1 << indent)
    }

    pub fn set(&mut self, bit: usize) {
        assert!(bit < self.bit_len);
        let (index, indent) = BitField::index(bit);

        self.u32s[index] |= 1 << indent
    }

    pub fn toggle(&mut self, bit: usize) {
        assert!(bit < self.bit_len);
        let (index, indent) = BitField::index(bit);

        self.u32s[index] ^= 1 << indent
    }

    pub fn get(&self, bit: usize) -> bool {
        assert!(bit < self.bit_len);
        let (index, indent) = BitField::index(bit);
        (self.u32s[index] >> indent) & 1 == 1
    }

    pub fn get_b(&self, bit: usize) -> u32 {
        assert!(bit < self.bit_len);
        let (index, indent) = BitField::index(bit);
        (self.u32s[index] >> indent) & 1
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
        for &i in &self.u32s {
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
        for &u in &self.u32s {
            if u != 0 {
                for _ in 0..32 {
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
                index += 32;
            }
        }

        res
    }

    pub fn get_ijs(&self, dim: ClockIndex, n_cons: usize) -> Vec<(usize, usize)> {
        //let dim = dim as u32;
        let mut ijs = Vec::with_capacity(n_cons);
        let mut found = 0;
        let mut i = 0usize;
        let mut j = 0usize;
        for &u in &self.u32s {
            let mut b = u;
            if b != 0 {
                for _ in 0..32 {
                    if (b & 1) == 1 {
                        while j >= dim {
                            j -= dim;
                            i += 1;
                        }
                        ijs.push((i, j));
                        found += 1;

                        if found > n_cons {
                            return ijs;
                        }
                    }
                    j += 1;
                    b >>= 1;
                }
            } else {
                j += 32;
            }
        }

        ijs
    }

    /*pub fn get_indices_satisfying<F>(
        self,
        dim: ClockIndex,
        n_constraints: u32,
        pred: F,
    ) -> Vec<usize>
    where
        F: Fn(u32, u32) -> bool,
    {
        let dim = dim as u32;
        let indices = vec![];
        let mut i = 0;
        let mut j = 0;
        let mut k = n_constraints;
        loop {
            let mut count = 32;
            for &b in &self.u32s {
                let mut b = b;
                if b == 0 {
                    continue;
                }

                while (b & 1) == 0 {
                    count -= 1;
                    b >>= 1;
                }

                fix_ij(&mut i, &mut j, dim);

                if pred(i, j) {
                    indices.push((i, j))
                }

                count -= 1;
                b >>= 1;
                j += 1;
            }
        }

        indices
    }*/
}

#[inline]
fn fix_ij(i: &mut u32, j: &mut u32, dim: u32) {
    while *j >= dim {
        *j -= dim;
        *i += 1
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

mod test {
    use std::fmt::Binary;

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
        assert_eq!(BitField::index(32), (1, 0));
        assert_eq!(BitField::index(0), (0, 0));
        assert_eq!(BitField::index(1), (0, 1));
        assert_eq!(BitField::index(33), (1, 1));
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
}
