use crate::types::int::{Int, ToInt};
use crate::division::{bezout, rem};

pub fn mod_inverse<T: ToInt, U: ToInt>(a: &T, m: &U) -> Int {
    let a = a.to_int();
    let m = m.to_int();
    if m.lt_int(2) {
        panic!("Modulus must be at least 2");
    }
    let b = bezout(&a, &m);
    rem(&b.x, &m)
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;
    use crate::division::{rem, gcd};

    proptest! {
        #[test]
        fn test_mod_inverse(a: i64, m: u64) {
            prop_assume!(m > 1);
            prop_assume!(gcd(&a, &m) == Int::from(1));
            let inv = mod_inverse(&a, &m);
            prop_assert!(inv.is_positive());
            let mult_result = rem(&(a * inv), &m);
            prop_assert_eq!(mult_result, Int::from(1));
        }
    }
}

