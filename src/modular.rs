use crate::int::Int;
use crate::division::{bezout};


pub fn mod_inverse(a: &Int, m: &Int) -> Int {
    if m.lt_i32(2) {
        panic!("Modulus must be at least 2");
    }
    let (x, _y) = bezout(&a, &m);
    if x.is_negative() { x + m } else { x }
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;
    use crate::division::{div_rem, gcd};

    proptest! {
        #[ignore]
        fn test_mod_inverse(a: i64, m: u64) {
            let a = Int::from(a);
            let m = Int::from(m);
            prop_assume!(m.ge_i32(2));
            prop_assume!(gcd(&a, &m) == Int::from(1));
            let inv = mod_inverse(&a, &m);
            let mult_result = div_rem(&inv, &m).1;
            prop_assert!(inv.is_positive());
            prop_assert_eq!(mult_result, Int::from(1));
        }
    }
}

