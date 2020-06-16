use std::{fmt, ops};
use std::cmp::Ordering;
use std::num::ParseIntError;
use std::str::FromStr;
use num::bigint::{BigInt, Sign};

#[derive(PartialEq, Eq, Debug, Clone)]
pub struct Int {
    value: BigInt,
}

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

// public methods

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

    pub fn gt_i32(&self, other: i32) -> bool {
        self.gt(&Int::from(other))
    }

    pub fn lt_i32(&self, other: i32) -> bool {
        self.lt(&Int::from(other))
    }

    pub fn ge_i32(&self, other: i32) -> bool {
        self.ge(&Int::from(other))
    }

    pub fn le_i32(&self, other: i32) -> bool {
        self.le(&Int::from(other))
    }
}

// +
impl_op_ex!(+ |a: &Int, b: &Int| -> Int { Int { value: a.value.clone() + b.value.clone() } });
impl_op_ex_commutative!(+ |a: &Int, b: &i32| -> Int { Int { value: a.value.clone() + b } });
impl_op_ex_commutative!(+ |a: &Int, b: &i64| -> Int { Int { value: a.value.clone() + b } });

// *
impl_op_ex!(* |a: &Int, b: &Int| -> Int { Int { value: a.value.clone() * b.value.clone() } });
impl_op_ex_commutative!(* |a: &Int, b: &i32| -> Int { Int { value: a.value.clone() * b } });
impl_op_ex_commutative!(* |a: &Int, b: &i64| -> Int { Int { value: a.value.clone() * b } });

// -
impl_op_ex!(- |a: &Int, b: &Int| -> Int { Int { value: a.value.clone() - b.value.clone() } });
impl_op_ex!(- |a: &Int, b: &i32| -> Int { Int { value: a.value.clone() - b } });
impl_op_ex!(- |a: &Int, b: &i64| -> Int { Int { value: a.value.clone() - b } });
impl_op_ex!(- |a: &i32, b: &Int| -> Int { Int { value: a - b.value.clone() } });
impl_op_ex!(- |a: &i64, b: &Int| -> Int { Int { value: a - b.value.clone() } });

// /
impl_op_ex!(/ |a: &Int, b: &Int| -> Int { Int { value: a.value.clone() / b.value.clone() } });
impl_op_ex!(/ |a: &Int, b: &i32| -> Int { Int { value: a.value.clone() / b } });
impl_op_ex!(/ |a: &Int, b: &i64| -> Int { Int { value: a.value.clone() / b } });
impl_op_ex!(/ |a: &i32, b: &Int| -> Int { Int { value: a / b.value.clone() } });
impl_op_ex!(/ |a: &i64, b: &Int| -> Int { Int { value: a / b.value.clone() } });

// %
impl_op_ex!(% |a: &Int, b: &Int| -> Int { Int { value: a.value.clone() % b.value.clone() } });
impl_op_ex!(% |a: &Int, b: &i32| -> Int { Int { value: a.value.clone() % b } });
impl_op_ex!(% |a: &Int, b: &i64| -> Int { Int { value: a.value.clone() % b } });
impl_op_ex!(% |a: &i32, b: &Int| -> Int { Int { value: a % b.value.clone() } });
impl_op_ex!(% |a: &i64, b: &Int| -> Int { Int { value: a % b.value.clone() } });

// building from primitive integers, big integers, and strings

impl From<i32> for Int {
    fn from(value: i32) -> Self {
        Self { value: BigInt::from(value) }
    }
}

impl From<u32> for Int {
    fn from(value: u32) -> Self {
        Self { value: BigInt::from(value) }
    }
}

impl From<i64> for Int {
    fn from(value: i64) -> Self {
        Self { value: BigInt::from(value) }
    }
}

impl From<u64> for Int {
    fn from(value: u64) -> Self {
        Self { value: BigInt::from(value) }
    }
}

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

trait ToInt {
    fn to_int(&self) -> Int;
}

impl ToInt for &str {
    fn to_int(&self) -> Int { Int::from_str(self).unwrap() }
}

impl ToInt for String {
    fn to_int(&self) -> Int { Int::from_str(self).unwrap() }
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    proptest! {
        #[test]
        fn test_add_int_int(a: i32, b: i32) {
            prop_assert_eq!(
                Int::from(a) + Int::from(b),
                Int::from(a as i64 + b as i64)
            );
        }

        #[test]
        fn test_add_int_i32(a: i32, b: i32) {
            prop_assert_eq!(
                Int::from(a) + b,
                Int::from(a as i64 + b as i64)
            );
            prop_assert_eq!(
                a + Int::from(b),
                Int::from(a as i64 + b as i64)
            );
        }

        #[test]
        fn test_add_int_i64(a: i32, b: i32) {
            let a = a as i64;
            let b = b as i64;
            prop_assert_eq!(
                Int::from(a) + b,
                Int::from(a + b)
            );
            prop_assert_eq!(
                a + Int::from(b),
                Int::from(a + b)
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
        fn test_mult_int_i32(a: i32, b: i32) {
            prop_assert_eq!(
                Int::from(a) * b,
                Int::from(a as i64 * b as i64)
            );
            prop_assert_eq!(
                a * Int::from(b),
                Int::from(a as i64 * b as i64)
            );
        }

        #[test]
        fn test_mult_int_i64(a: i32, b: i32) {
            let a = a as i64;
            let b = b as i64;
            prop_assert_eq!(
                Int::from(a) * b,
                Int::from(a * b)
            );
            prop_assert_eq!(
                a * Int::from(b),
                Int::from(a * b)
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
        fn test_sub_int_i32(a: i32, b: i32) {
            prop_assert_eq!(
                Int::from(a) - b,
                Int::from(a as i64 - b as i64)
            );
            prop_assert_eq!(
                a - Int::from(b),
                Int::from(a as i64 - b as i64)
            );
        }

        #[test]
        fn test_sub_int_i64(a: i32, b: i32) {
            let a = a as i64;
            let b = b as i64;
            prop_assert_eq!(
                Int::from(a) - b,
                Int::from(a - b)
            );
            prop_assert_eq!(
                a - Int::from(b),
                Int::from(a - b)
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
        fn test_div_int_i32(a: i32, b: i32) {
            prop_assert_eq!(
                Int::from(a) / b,
                Int::from(a as i64 / b as i64)
            );
            prop_assert_eq!(
                a / Int::from(b),
                Int::from(a as i64 / b as i64)
            );
        }

        #[test]
        fn test_div_int_i64(a: i32, b: i32) {
            let a = a as i64;
            let b = b as i64;
            prop_assert_eq!(
                Int::from(a) / b,
                Int::from(a / b)
            );
            prop_assert_eq!(
                a / Int::from(b),
                Int::from(a / b)
            );
        }

        #[test]
        fn test_mod_int_int(a: i32, b: i32) {
            prop_assert_eq!(
                Int::from(a) % Int::from(b),
                Int::from(a as i64 % b as i64)
            );
        }

        #[test]
        fn test_mod_int_i32(a: i32, b: i32) {
            prop_assert_eq!(
                Int::from(a) % b,
                Int::from(a as i64 % b as i64)
            );
            prop_assert_eq!(
                a % Int::from(b),
                Int::from(a as i64 % b as i64)
            );
        }

        #[test]
        fn test_mod_int_i64(a: i32, b: i32) {
            let a = a as i64;
            let b = b as i64;
            prop_assert_eq!(
                Int::from(a) % b,
                Int::from(a % b)
            );
            prop_assert_eq!(
                a % Int::from(b),
                Int::from(a % b)
            );
        }
    }

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
    }

    #[test]
    fn test_display() {
        let pos = "19287349187324901237492817349827349182734";
        assert_eq!(format!("{}", pos.to_int()), String::from(pos));
        let neg = "-1203948102938402193840912340981034980198";
        assert_eq!(format!("{}", neg.to_int()), String::from(neg));
    }

    #[test]
    fn test_from_i32() {
        let a: i32 = 123456789;
        assert_eq!(Int::from(a).value, BigInt::from(a));
    }

    #[test]
    fn test_from_u32() {
        let a: u32 = 123456789;
        assert_eq!(Int::from(a).value, BigInt::from(a));
    }

    #[test]
    fn test_from_i64() {
        let a: i64 = 123456789;
        assert_eq!(Int::from(a).value, BigInt::from(a));
    }

    #[test]
    fn test_from_u64() {
        let a: u64 = 123456789;
        assert_eq!(Int::from(a).value, BigInt::from(a));
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
}
