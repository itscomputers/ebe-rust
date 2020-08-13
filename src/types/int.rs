use std::{fmt, ops};
use std::cmp::Ordering;
use std::num::ParseIntError;
use std::str::FromStr;
use num::bigint::{BigInt, Sign};

use crate::division::{gcd};

#[derive(PartialEq, Eq, Debug, Clone)]
pub struct Int {
    value: BigInt,
}

//----------------------------------------------------------
// standard traits

impl fmt::Display for Int {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.value.to_str_radix(10))
    }
}

impl Ord for Int {
    fn cmp(&self, other: &Int) -> Ordering {
        self.value.cmp(&other.value)
    }
}

impl PartialOrd for Int {
    fn partial_cmp(&self, other: &Int) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl ops::Neg for Int {
    type Output = Int;

    fn neg(self) -> Self::Output { Self { value: -self.value.clone() } }
}

//----------------------------------------------------------
// public traits

impl Int {
    pub fn signum(&self) -> i32 {
        match self.value.sign() {
            Sign::Minus => -1,
            Sign::NoSign => 0,
            _ => 1,
        }
    }

    pub fn abs(&self) -> Self {
        let value = if self.is_negative() { -self.value.clone() } else { self.value.clone() };
        Self { value }
    }

    pub fn gcd<T: ToInt>(&self, other: &T) -> Self {
        gcd(self, &other.to_int())
    }

    pub fn is_positive(&self) -> bool {
        match self.value.sign() {
            Sign::Plus => true,
            _ => false,
        }
    }

    pub fn is_negative(&self) -> bool {
        match self.value.sign() {
            Sign::Minus => true,
            _ => false,
        }
    }

    pub fn is_zero(&self) -> bool {
        match self.value.sign() {
            Sign::NoSign => true,
            _ => false,
        }
    }

    pub fn is_nonzero(&self) -> bool {
        match self.value.sign() {
            Sign::NoSign => false,
            _ => true,
        }
    }

    pub fn gt_int<T: ToInt>(&self, other: T) -> bool {
        self.gt(&other.to_int())
    }

    pub fn lt_int<T: ToInt>(&self, other: T) -> bool {
        self.lt(&other.to_int())
    }

    pub fn ge_int<T: ToInt>(&self, other: T) -> bool {
        self.ge(&other.to_int())
    }

    pub fn le_int<T: ToInt>(&self, other: T) -> bool {
        self.le(&other.to_int())
    }

    pub fn eq_int<T: ToInt>(&self, other: T) -> bool {
        self.eq(&other.to_int())
    }

    pub fn ne_int<T: ToInt>(&self, other: T) -> bool {
        self.ne(&other.to_int())
    }
}

//----------------------------------------------------------
// initialization

macro_rules! impl_int_from {
    (for $($t:ty),+) => {
        $(impl From<$t> for Int {
            fn from(value: $t) -> Self { Self { value: BigInt::from(value) } }
        })*
    }
}
impl_int_from!(for i8, u8, i16, u16, i32, u32, i64, u64, isize, usize);

impl From<BigInt> for Int {
    fn from(value: BigInt) -> Self {
        Self { value }
    }
}

impl FromStr for Int {
    type Err = ParseIntError;

    fn from_str(value: &str) -> Result<Self, Self::Err> {
        Ok(Self { value: BigInt::from_str(value).unwrap() })
    }
}

pub trait ToInt {
    fn to_int(&self) -> Int;
}

impl ToInt for &str {
    fn to_int(&self) -> Int { Int::from_str(self).unwrap() }
}

impl ToInt for String {
    fn to_int(&self) -> Int { Int::from_str(self).unwrap() }
}

macro_rules! impl_to_int {
    (for $($t:ty),+) => {
        $(impl ToInt for $t { fn to_int(&self) -> Int { Int::from(self.clone()) } })*
    }
}
impl_to_int!(for i8, u8, i16, u16, i32, u32, i64, u64, isize, usize, BigInt, Int);

//----------------------------------------------------------
// operations

macro_rules! op_other {
    ($op:tt, $int:ident, $other:ident) => ($int $op Int::from($other.clone()))
}
macro_rules! op_other_reverse {
    ($op:tt, $other:ident, $int:ident) => (Int::from($other.clone()) $op $int)
}

// addition
impl_op_ex!(+ |a: &Int, b: &Int| -> Int { Int { value: a.value.clone() + b.value.clone() } });
impl_op_ex_commutative!(+ |a: &Int, b: &i8| -> Int { op_other!(+, a, b) });
impl_op_ex_commutative!(+ |a: &Int, b: &u8| -> Int { op_other!(+, a, b) });
impl_op_ex_commutative!(+ |a: &Int, b: &i16| -> Int { op_other!(+, a, b) });
impl_op_ex_commutative!(+ |a: &Int, b: &u16| -> Int { op_other!(+, a, b) });
impl_op_ex_commutative!(+ |a: &Int, b: &i32| -> Int { op_other!(+, a, b) });
impl_op_ex_commutative!(+ |a: &Int, b: &u32| -> Int { op_other!(+, a, b) });
impl_op_ex_commutative!(+ |a: &Int, b: &i64| -> Int { op_other!(+, a, b) });
impl_op_ex_commutative!(+ |a: &Int, b: &u64| -> Int { op_other!(+, a, b) });
impl_op_ex_commutative!(+ |a: &Int, b: &isize| -> Int { op_other!(+, a, b) });
impl_op_ex_commutative!(+ |a: &Int, b: &usize| -> Int { op_other!(+, a, b) });

// multiplication
impl_op_ex!(* |a: &Int, b: &Int| -> Int { Int { value: a.value.clone() * b.value.clone() } });
impl_op_ex_commutative!(* |a: &Int, b: &i8| -> Int { op_other!(*, a, b) });
impl_op_ex_commutative!(* |a: &Int, b: &u8| -> Int { op_other!(*, a, b) });
impl_op_ex_commutative!(* |a: &Int, b: &i16| -> Int { op_other!(*, a, b) });
impl_op_ex_commutative!(* |a: &Int, b: &u16| -> Int { op_other!(*, a, b) });
impl_op_ex_commutative!(* |a: &Int, b: &i32| -> Int { op_other!(*, a, b) });
impl_op_ex_commutative!(* |a: &Int, b: &u32| -> Int { op_other!(*, a, b) });
impl_op_ex_commutative!(* |a: &Int, b: &i64| -> Int { op_other!(*, a, b) });
impl_op_ex_commutative!(* |a: &Int, b: &u64| -> Int { op_other!(*, a, b) });
impl_op_ex_commutative!(* |a: &Int, b: &isize| -> Int { op_other!(*, a, b) });
impl_op_ex_commutative!(* |a: &Int, b: &usize| -> Int { op_other!(*, a, b) });

// subtraction
impl_op_ex!(- |a: &Int, b: &Int| -> Int { Int { value: a.value.clone() - b.value.clone() } });
impl_op_ex!(- |a: &Int, b: &i8| -> Int { op_other!(-, a, b) });
impl_op_ex!(- |a: &Int, b: &u8| -> Int { op_other!(-, a, b) });
impl_op_ex!(- |a: &Int, b: &i16| -> Int { op_other!(-, a, b) });
impl_op_ex!(- |a: &Int, b: &u16| -> Int { op_other!(-, a, b) });
impl_op_ex!(- |a: &Int, b: &i32| -> Int { op_other!(-, a, b) });
impl_op_ex!(- |a: &Int, b: &u32| -> Int { op_other!(-, a, b) });
impl_op_ex!(- |a: &Int, b: &i64| -> Int { op_other!(-, a, b) });
impl_op_ex!(- |a: &Int, b: &u64| -> Int { op_other!(-, a, b) });
impl_op_ex!(- |a: &Int, b: &isize| -> Int { op_other!(-, a, b) });
impl_op_ex!(- |a: &Int, b: &usize| -> Int { op_other!(-, a, b) });
impl_op_ex!(- |a: &i8, b: &Int| -> Int { op_other_reverse!(-, a, b) });
impl_op_ex!(- |a: &u8, b: &Int| -> Int { op_other_reverse!(-, a, b) });
impl_op_ex!(- |a: &i16, b: &Int| -> Int { op_other_reverse!(-, a, b) });
impl_op_ex!(- |a: &u16, b: &Int| -> Int { op_other_reverse!(-, a, b) });
impl_op_ex!(- |a: &i32, b: &Int| -> Int { op_other_reverse!(-, a, b) });
impl_op_ex!(- |a: &u32, b: &Int| -> Int { op_other_reverse!(-, a, b) });
impl_op_ex!(- |a: &i64, b: &Int| -> Int { op_other_reverse!(-, a, b) });
impl_op_ex!(- |a: &u64, b: &Int| -> Int { op_other_reverse!(-, a, b) });
impl_op_ex!(- |a: &isize, b: &Int| -> Int { op_other_reverse!(-, a, b) });
impl_op_ex!(- |a: &usize, b: &Int| -> Int { op_other_reverse!(-, a, b) });

// division
impl_op_ex!(/ |a: &Int, b: &Int| -> Int { Int { value: a.value.clone() / b.value.clone() } });
impl_op_ex!(/ |a: &Int, b: &i8| -> Int { op_other!(/, a, b) });
impl_op_ex!(/ |a: &Int, b: &u8| -> Int { op_other!(/, a, b) });
impl_op_ex!(/ |a: &Int, b: &i16| -> Int { op_other!(/, a, b) });
impl_op_ex!(/ |a: &Int, b: &u16| -> Int { op_other!(/, a, b) });
impl_op_ex!(/ |a: &Int, b: &i32| -> Int { op_other!(/, a, b) });
impl_op_ex!(/ |a: &Int, b: &u32| -> Int { op_other!(/, a, b) });
impl_op_ex!(/ |a: &Int, b: &i64| -> Int { op_other!(/, a, b) });
impl_op_ex!(/ |a: &Int, b: &u64| -> Int { op_other!(/, a, b) });
impl_op_ex!(/ |a: &Int, b: &isize| -> Int { op_other!(/, a, b) });
impl_op_ex!(/ |a: &Int, b: &usize| -> Int { op_other!(/, a, b) });
impl_op_ex!(/ |a: &i8, b: &Int| -> Int { op_other_reverse!(/, a, b) });
impl_op_ex!(/ |a: &u8, b: &Int| -> Int { op_other_reverse!(/, a, b) });
impl_op_ex!(/ |a: &i16, b: &Int| -> Int { op_other_reverse!(/, a, b) });
impl_op_ex!(/ |a: &u16, b: &Int| -> Int { op_other_reverse!(/, a, b) });
impl_op_ex!(/ |a: &i32, b: &Int| -> Int { op_other_reverse!(/, a, b) });
impl_op_ex!(/ |a: &u32, b: &Int| -> Int { op_other_reverse!(/, a, b) });
impl_op_ex!(/ |a: &i64, b: &Int| -> Int { op_other_reverse!(/, a, b) });
impl_op_ex!(/ |a: &u64, b: &Int| -> Int { op_other_reverse!(/, a, b) });
impl_op_ex!(/ |a: &isize, b: &Int| -> Int { op_other_reverse!(/, a, b) });
impl_op_ex!(/ |a: &usize, b: &Int| -> Int { op_other_reverse!(/, a, b) });

// remainder
impl_op_ex!(% |a: &Int, b: &Int| -> Int { Int { value: a.value.clone() % b.value.clone() } });
impl_op_ex!(% |a: &Int, b: &i8| -> Int { op_other!(%, a, b) });
impl_op_ex!(% |a: &Int, b: &u8| -> Int { op_other!(%, a, b) });
impl_op_ex!(% |a: &Int, b: &i16| -> Int { op_other!(%, a, b) });
impl_op_ex!(% |a: &Int, b: &u16| -> Int { op_other!(%, a, b) });
impl_op_ex!(% |a: &Int, b: &i32| -> Int { op_other!(%, a, b) });
impl_op_ex!(% |a: &Int, b: &u32| -> Int { op_other!(%, a, b) });
impl_op_ex!(% |a: &Int, b: &i64| -> Int { op_other!(%, a, b) });
impl_op_ex!(% |a: &Int, b: &u64| -> Int { op_other!(%, a, b) });
impl_op_ex!(% |a: &Int, b: &isize| -> Int { op_other!(%, a, b) });
impl_op_ex!(% |a: &Int, b: &usize| -> Int { op_other!(%, a, b) });
impl_op_ex!(% |a: &i8, b: &Int| -> Int { op_other_reverse!(%, a, b) });
impl_op_ex!(% |a: &u8, b: &Int| -> Int { op_other_reverse!(%, a, b) });
impl_op_ex!(% |a: &i16, b: &Int| -> Int { op_other_reverse!(%, a, b) });
impl_op_ex!(% |a: &u16, b: &Int| -> Int { op_other_reverse!(%, a, b) });
impl_op_ex!(% |a: &i32, b: &Int| -> Int { op_other_reverse!(%, a, b) });
impl_op_ex!(% |a: &u32, b: &Int| -> Int { op_other_reverse!(%, a, b) });
impl_op_ex!(% |a: &i64, b: &Int| -> Int { op_other_reverse!(%, a, b) });
impl_op_ex!(% |a: &u64, b: &Int| -> Int { op_other_reverse!(%, a, b) });
impl_op_ex!(% |a: &isize, b: &Int| -> Int { op_other_reverse!(%, a, b) });
impl_op_ex!(% |a: &usize, b: &Int| -> Int { op_other_reverse!(%, a, b) });

//==========================================================

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    macro_rules! test_comparison {
        ($name:ident, $t:ty) => {
            #[test]
            fn $name() {
                let small = 5 as $t;
                let large = 69 as $t;
                assert!(Int::from(small).eq_int(small));
                assert!(Int::from(small).ne_int(large));

                assert!(Int::from(small).lt_int(large));
                assert!(Int::from(small).le_int(large));
                assert!(Int::from(small).le_int(small));

                assert!(Int::from(large).gt_int(small));
                assert!(Int::from(large).ge_int(small));
                assert!(Int::from(large).ge_int(large));
            }
        }
    }
    test_comparison!(test_comparison_to_i8, i8);
    test_comparison!(test_comparison_to_u8, u8);
    test_comparison!(test_comparison_to_i16, i16);
    test_comparison!(test_comparison_to_u16, u16);
    test_comparison!(test_comparison_to_i32, i32);
    test_comparison!(test_comparison_to_u32, u32);
    test_comparison!(test_comparison_to_i64, i64);
    test_comparison!(test_comparison_to_u64, u64);
    test_comparison!(test_comparison_to_isize, isize);
    test_comparison!(test_comparison_to_usize, usize);

    #[test]
    fn test_signed() {
        let positive = Int::from(123456789);
        let negative = Int::from(-123456789);
        let zero = Int::from(0);

        assert_eq!(positive.signum(), 1);
        assert_eq!(negative.signum(), -1);
        assert_eq!(zero.signum(), 0);

        assert_eq!(positive.abs(), positive);
        assert_eq!(negative.abs(), positive);
        assert_eq!(zero.abs(), zero);

        assert!(positive.is_positive());
        assert!(!negative.is_positive());
        assert!(!zero.is_positive());

        assert!(!positive.is_negative());
        assert!(negative.is_negative());
        assert!(!zero.is_negative());

        assert_eq!(-positive.clone(), negative.clone());
        assert_eq!(positive, -negative);
    }

    proptest! {
        #[test]
        fn test_gcd(a: i64, b: i64) {
            prop_assume!(a != 0 || b != 0);
            prop_assert_eq!(Int::from(a.clone()).gcd(&b), gcd(&a, &b));
        }
    }

    #[test]
    fn test_display() {
        let pos = "19287349187324901237492817349827349182734";
        assert_eq!(format!("{}", pos.to_int()), String::from(pos));
        let neg = "-1203948102938402193840912340981034980198";
        assert_eq!(format!("{}", neg.to_int()), String::from(neg));
    }

    #[test]
    fn test_from_bigint() {
        let a = BigInt::from(123456789);
        assert_eq!(Int::from(a.clone()).value, a);
    }

    #[test]
    fn test_from_str() {
        assert_eq!(Int::from_str("123456789").unwrap().value, BigInt::from(123456789));
    }

    #[test]
    fn test_from_string() {
        let a = 123456789;
        assert_eq!(Int::from_str(&a.to_string()).unwrap().value, BigInt::from(a));
    }

    #[test]
    fn test_str_to_int() {
        assert_eq!("123456789".to_int().value, BigInt::from(123456789));
    }

    #[test]
    fn test_string_to_int() {
        assert_eq!(String::from("123456789").to_int().value, BigInt::from(123456789));
    }

    macro_rules! test_from_primitive {
        ($name:ident, $t:ty) => (
            #[test]
            fn $name() {
                let a = 100 as $t;
                assert_eq!(Int::from(a).value, BigInt::from(a));
                assert_eq!(a.to_int().value, BigInt::from(a));
            }
        )
    }

    test_from_primitive!(test_from_i8, i8);
    test_from_primitive!(test_from_u8, u8);
    test_from_primitive!(test_from_i16, i16);
    test_from_primitive!(test_from_u16, u16);
    test_from_primitive!(test_from_i32, i32);
    test_from_primitive!(test_from_u32, u32);
    test_from_primitive!(test_from_i64, i64);
    test_from_primitive!(test_from_u64, u64);
    test_from_primitive!(test_from_isize, isize);
    test_from_primitive!(test_from_usize, usize);

    macro_rules! test_op_int_primitive {
        ($name:ident, $t:ty, $op:tt) => (
            #[test]
            fn $name() {
                let a = 100 as $t;
                let b = 69 as $t;
                let value = Int::from(a as i64 $op b as i64);
                assert_eq!(Int::from(a) $op b, value);
                assert_eq!(a $op Int::from(b), value);
            }
        )
    }

    test_op_int_primitive!(test_add_int_i8, i8, +);
    test_op_int_primitive!(test_add_int_u8, u8, +);
    test_op_int_primitive!(test_add_int_i16, i16, +);
    test_op_int_primitive!(test_add_int_u16, u16, +);
    test_op_int_primitive!(test_add_int_i32, i32, +);
    test_op_int_primitive!(test_add_int_u32, u32, +);
    test_op_int_primitive!(test_add_int_i64, i64, +);
    test_op_int_primitive!(test_add_int_u64, u64, +);
    test_op_int_primitive!(test_add_int_isize, isize, +);
    test_op_int_primitive!(test_add_int_usize, usize, +);

    test_op_int_primitive!(test_mul_int_i8, i8, *);
    test_op_int_primitive!(test_mul_int_u8, u8, *);
    test_op_int_primitive!(test_mul_int_i16, i16, *);
    test_op_int_primitive!(test_mul_int_u16, u16, *);
    test_op_int_primitive!(test_mul_int_i32, i32, *);
    test_op_int_primitive!(test_mul_int_u32, u32, *);
    test_op_int_primitive!(test_mul_int_i64, i64, *);
    test_op_int_primitive!(test_mul_int_u64, u64, *);
    test_op_int_primitive!(test_mul_int_isize, isize, *);
    test_op_int_primitive!(test_mul_int_usize, usize, *);

    test_op_int_primitive!(test_sub_int_i8, i8, -);
    test_op_int_primitive!(test_sub_int_u8, u8, -);
    test_op_int_primitive!(test_sub_int_i16, i16, -);
    test_op_int_primitive!(test_sub_int_u16, u16, -);
    test_op_int_primitive!(test_sub_int_i32, i32, -);
    test_op_int_primitive!(test_sub_int_u32, u32, -);
    test_op_int_primitive!(test_sub_int_i64, i64, -);
    test_op_int_primitive!(test_sub_int_u64, u64, -);
    test_op_int_primitive!(test_sub_int_isize, isize, -);
    test_op_int_primitive!(test_sub_int_usize, usize, -);

    test_op_int_primitive!(test_div_int_i8, i8, /);
    test_op_int_primitive!(test_div_int_u8, u8, /);
    test_op_int_primitive!(test_div_int_i16, i16, /);
    test_op_int_primitive!(test_div_int_u16, u16, /);
    test_op_int_primitive!(test_div_int_i32, i32, /);
    test_op_int_primitive!(test_div_int_u32, u32, /);
    test_op_int_primitive!(test_div_int_i64, i64, /);
    test_op_int_primitive!(test_div_int_u64, u64, /);
    test_op_int_primitive!(test_div_int_isize, isize, /);
    test_op_int_primitive!(test_div_int_usize, usize, /);

    test_op_int_primitive!(test_mod_int_i8, i8, %);
    test_op_int_primitive!(test_mod_int_u8, u8, %);
    test_op_int_primitive!(test_mod_int_i16, i16, %);
    test_op_int_primitive!(test_mod_int_u16, u16, %);
    test_op_int_primitive!(test_mod_int_i32, i32, %);
    test_op_int_primitive!(test_mod_int_u32, u32, %);
    test_op_int_primitive!(test_mod_int_i64, i64, %);
    test_op_int_primitive!(test_mod_int_u64, u64, %);
    test_op_int_primitive!(test_mod_int_isize, isize, %);
    test_op_int_primitive!(test_mod_int_usize, usize, %);

    proptest! {
        #[test]
        fn test_add_int_int(a: i32, b: i32) {
            prop_assert_eq!(
                Int::from(a) + Int::from(b),
                Int::from(a as i64 + b as i64)
            );
        }

        #[test]
        fn test_mult_int_int(a: i32, b: i32) {
            prop_assert_eq!(
                Int::from(a) * Int::from(b),
                Int::from(a as i64 * b as i64)
            );
        }

        #[test]
        fn test_sub_int_int(a: i32, b: i32) {
            prop_assert_eq!(
                Int::from(a) - Int::from(b),
                Int::from(a as i64 - b as i64)
            );
        }

        #[test]
        fn test_div_int_int(a: i32, b: i32) {
            prop_assert_eq!(
                Int::from(a) / Int::from(b),
                Int::from(a as i64 / b as i64)
            );
        }

        #[test]
        fn test_mod_int_int(a: i32, b: i32) {
            prop_assert_eq!(
                Int::from(a) % Int::from(b),
                Int::from(a as i64 % b as i64)
            );
        }
    }
}
