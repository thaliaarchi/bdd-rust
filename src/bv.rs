//! Bit vector type.

use std::{
    fmt::{self, Debug, Formatter},
    iter::repeat_n,
    ops::{Add, AddAssign, Mul},
};

use crate::{Bdd, BddId, BddManager};

// TODO:
// - Implement multiply assign.

/// An unsigned bit vector.
#[derive(Clone)]
pub struct Bv<'mgr> {
    bits: Box<[BddId]>,
    mgr: &'mgr BddManager,
}

impl<'mgr> Bv<'mgr> {
    /// Constructs a bit vector as a variable with a given size.
    pub fn new_var(mgr: &'mgr BddManager, name: &str, size: usize) -> Self {
        let bits = (0..size)
            .map(|i| mgr.variable(format!("{name}{i}")).id())
            .collect();
        Bv { bits, mgr }
    }

    /// Constructs a bit vector from a constant value with a given size.
    pub fn new_const(mgr: &'mgr BddManager, c: u64, size: usize) -> Self {
        let mut bits = repeat_n(BddId::ZERO, size).collect::<Box<[_]>>();
        for i in 0..size.min(u64::BITS as usize) {
            bits[i] = BddId::from(c & (1 << i) != 0);
        }
        Bv { bits, mgr }
    }

    /// Converts the bit vector to a constant, if it represents only a single
    /// value.
    pub fn as_const(&self) -> Option<u64> {
        let mut c = 0;
        for (i, x) in self.bits.iter().enumerate() {
            let Some(b) = x.as_const() else {
                return None;
            };
            if i < u64::BITS as usize {
                c |= (b as u64) << i;
            }
        }
        Some(c)
    }

    /// Gets the bit at the given index.
    pub fn get(&self, i: usize) -> Bdd<'mgr> {
        self.mgr.wrap(self.bits[i])
    }

    /// Sets the bit at the given index.
    pub fn set(&mut self, i: usize, value: Bdd<'mgr>) {
        Bdd::assert_manager(self.mgr, value.mgr);
        self.bits[i] = value.id();
    }

    /// Returns the number of bits.
    pub fn size(&self) -> usize {
        self.bits.len()
    }

    /// Returns the manager for this bit vector.
    pub fn manager(&self) -> &'mgr BddManager {
        self.mgr
    }
}

impl Debug for Bv<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "Bv<{}>", self.size())?;
        if let Some(c) = self.as_const() {
            write!(f, "({c})")
        } else {
            f.debug_list()
                .entries(self.bits.iter().map(|&x| self.mgr.wrap(x)))
                .finish()
        }
    }
}

/// Implements bit vector addition, variable over destination, which can alias
/// $x or $y.
macro_rules! bv_add(($mgr:ident, $x:ident, $y:ident, $z:ident) => {{
    let len = $x.len();
    assert!(len == $y.len() && len == $z.len());
    if len < 2 {
        if len == 1 {
            $z[0] = $mgr.xor($x[0], $y[0]);
        }
        return;
    }
    let (z0, mut c) = $mgr.add_carry($x[0], $y[0]);
    $z[0] = z0;
    let last = len - 1;
    for i in 1..last {
        let (zi, ci) = $mgr.add_carry_in($x[i], $y[i], c);
        $z[i] = zi;
        c = ci;
    }
    $z[last] = $mgr.xor($mgr.xor($x[last], $y[last]), c);
}});

impl BddManager {
    /// Computes addition of two bit vectors.
    fn bv_add(&self, x: &[BddId], y: &[BddId], z: &mut [BddId]) {
        bv_add!(self, x, y, z);
    }

    /// Computes in-place addition of two bit vectors.
    fn bv_add_assign(&self, x: &mut [BddId], y: &[BddId]) {
        bv_add!(self, x, y, x);
    }

    /// Computes multiplication of two bit vectors.
    fn bv_mul(&self, x: &[BddId], y: &[BddId], z: &mut [BddId]) {
        let len = x.len();
        assert!(len == y.len() && len == z.len());
        for i in 0..len {
            z[i] = self.and(x[0], y[i]);
        }
        if len < 2 {
            return;
        }
        for i in 1..len {
            let (zi, mut c) = self.add_carry(self.and(x[i], y[0]), z[i]);
            z[i] = zi;
            for j in i + 1..len {
                let (zj, cj) = self.add_carry_in(self.and(x[i], y[j - i]), z[j], c);
                z[j] = zj;
                c = cj;
            }
        }
    }
}

impl<'mgr> Add for &Bv<'mgr> {
    type Output = Bv<'mgr>;

    fn add(self, rhs: Self) -> Self::Output {
        Bdd::assert_manager(self.mgr, rhs.mgr);
        let mut dest = Bv::new_const(self.mgr, 0, self.size());
        self.mgr.bv_add(&self.bits, &rhs.bits, &mut dest.bits);
        dest
    }
}

impl AddAssign<&Self> for Bv<'_> {
    fn add_assign(&mut self, rhs: &Self) {
        Bdd::assert_manager(self.mgr, rhs.mgr);
        self.mgr.bv_add_assign(&mut self.bits, &rhs.bits);
    }
}

impl<'mgr> Mul for &Bv<'mgr> {
    type Output = Bv<'mgr>;

    fn mul(self, rhs: Self) -> Self::Output {
        Bdd::assert_manager(self.mgr, rhs.mgr);
        let mut dest = Bv::new_const(self.mgr, 0, self.size());
        self.mgr.bv_mul(&self.bits, &rhs.bits, &mut dest.bits);
        dest
    }
}

#[cfg(test)]
mod tests {
    use std::ops::{Add, Mul};

    use crate::{bv::Bv, BddManager};

    macro_rules! test_op_const(($test:ident, $trait:ident :: $op:ident, $const_op:ident) => {
        #[test]
        fn $test() {
            const SIZE: usize = 7;
            const MAX: u64 = (1 << SIZE) - 1;
            let mgr = BddManager::new();
            for xc in 0..=MAX {
                for yc in 0..=MAX {
                    let x = Bv::new_const(&mgr, xc, SIZE);
                    let y = Bv::new_const(&mgr, yc, SIZE);
                    let z = $trait::$op(&x, &y);
                    if z.as_const() != Some(xc.$const_op(yc) & MAX) {
                        panic!("{}({xc}, {yc}) = {z:?}", stringify!($op));
                    }
                }
            }
        }
    });

    test_op_const!(add_const, Add::add, wrapping_add);
    test_op_const!(mul_const, Mul::mul, wrapping_mul);
}
