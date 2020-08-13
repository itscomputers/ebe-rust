use std::{fmt, ops};
use std::cmp::Ordering;
use std::num::ParseIntError;
use std::str::FromStr;

use crate::types::int::{Int, ToInt};
use crate::division::{gcd, div};

#[derive(Debug, Clone)]
struct Rational {
    numer: Int,
    denom: Int,
}

//----------------------------------------------------------
// standard traits

impl fmt::Display for Rational {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match &self.denom {
            d if d == &Int::from(1) => write!(f, "{}", self.numer),
            _ => write!(f, "{}/{}", self.numer, self.denom)
        }
    }
}

impl Ord for Rational {
    fn cmp(&self, other: &Rational) -> Ordering {
        (&self.numer * &other.denom).cmp(&(&self.denom * &other.numer))
    }
}

impl PartialOrd for Rational {
    fn partial_cmp(&self, other: &Rational) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl PartialEq for Rational {
    fn eq(&self, other: &Self) -> bool {
        (&self.numer * &other.denom).eq(&(&self.denom * &other.numer))
    }
}

impl Eq for Rational {}

impl ops::Neg for Rational {
    type Output = Rational;

    fn neg(self) -> Self::Output {
        Self { numer: -self.numer, denom: self.denom }
    }
}

//----------------------------------------------------------
// public traits

impl Rational {
    pub fn new<T: ToInt, U: ToInt>(numer: T, denom: U) -> Rational {
        let numer = numer.to_int();
        let denom = denom.to_int();

        if denom.is_zero() { panic!("{}/0 is undefined", numer); }

        let d = gcd(&numer, &denom);
        match (numer / &d, denom / &d) {
            (a, _b) if a.is_zero() => Rational { numer: a, denom: Int::from(1) },
            (a, b) if b.is_negative() => Rational { numer: -a, denom: -b },
            (a, b) => Rational { numer: a, denom: b },
        }
    }

    pub fn abs(&self) -> Self {
        Self { numer: self.numer.abs(), denom: self.denom.clone() }
    }

    pub fn reciprocal(&self) -> Self {
        if self.numer.is_negative() {
            Self { numer: -self.denom.clone(), denom: -self.numer.clone() }
        } else {
            Self { numer: self.denom.clone(), denom: self.numer.clone() }
        }
    }

    pub fn floor(&self) -> Int {
        div(&self.numer, &self.denom)
    }

    pub fn round(&self) -> Int {
        (self + Rational::new(1, 2)).floor()
    }
}

//----------------------------------------------------------
// initialization

macro_rules! impl_From {
    (for $($t:ty),+) => {
        $(impl From<$t> for Rational {
            fn from(value: $t) -> Self {
                Self { numer: Int::from(value), denom: Int::from(1) }
            }
        })*
    }
}
impl_From!(for i8, u8, i16, u16, i32, u32, i64, u64, isize, usize, Int);

impl FromStr for Rational {
    type Err = ParseIntError;

    fn from_str(value: &str) -> Result<Self, Self::Err> {
        let v: Vec<String> = value.split("/").map(|x| x.replace(" ", "")).collect();

        match v.len() {
            1 => Ok(Self {
                numer: Int::from_str(&v[0]).unwrap(),
                denom: Int::from(1),
            }),
            2 => Ok(Self {
                numer: Int::from_str(&v[0]).unwrap(),
                denom: Int::from_str(&v[1]).unwrap(),
            }),
            _ => panic!("Could not parse {} as rational", value),
        }
    }
}

// ---------------------------------------------------------
// operations

macro_rules! op_other {
    ($op:tt, $rational:ident, $primitive:ident) => ($rational $op Rational::from($primitive.clone()))
}
macro_rules! op_other_reverse {
    ($op:tt, $primitive:ident, $rational:ident) => (Rational::from($primitive.clone()) $op $rational)
}

// addition
impl_op_ex!(+ |a: &Rational, b: &Rational| -> Rational {
    let numer = &a.numer * &b.denom + &a.denom * &b.numer;
    let denom = &a.denom * &b.denom;
    Rational::new(numer, denom)
});
impl_op_ex_commutative!(+ |a: &Rational, b: &i8| -> Rational { op_other!(+, a, b) });
impl_op_ex_commutative!(+ |a: &Rational, b: &u8| -> Rational { op_other!(+, a, b) });
impl_op_ex_commutative!(+ |a: &Rational, b: &i16| -> Rational { op_other!(+, a, b) });
impl_op_ex_commutative!(+ |a: &Rational, b: &u16| -> Rational { op_other!(+, a, b) });
impl_op_ex_commutative!(+ |a: &Rational, b: &i32| -> Rational { op_other!(+, a, b) });
impl_op_ex_commutative!(+ |a: &Rational, b: &u32| -> Rational { op_other!(+, a, b) });
impl_op_ex_commutative!(+ |a: &Rational, b: &i64| -> Rational { op_other!(+, a, b) });
impl_op_ex_commutative!(+ |a: &Rational, b: &u64| -> Rational { op_other!(+, a, b) });
impl_op_ex_commutative!(+ |a: &Rational, b: &isize| -> Rational { op_other!(+, a, b) });
impl_op_ex_commutative!(+ |a: &Rational, b: &usize| -> Rational { op_other!(+, a, b) });
impl_op_ex_commutative!(+ |a: &Rational, b: &Int| -> Rational { op_other!(+, a, b) });

// multiplication
impl_op_ex!(* |a: &Rational, b: &Rational| -> Rational {
    let numer = &a.numer * &b.numer;
    let denom = &a.denom * &b.denom;
    Rational::new(numer, denom)
});
impl_op_ex_commutative!(* |a: &Rational, b: &i8| -> Rational { op_other!(*, a, b) });
impl_op_ex_commutative!(* |a: &Rational, b: &u8| -> Rational { op_other!(*, a, b) });
impl_op_ex_commutative!(* |a: &Rational, b: &i16| -> Rational { op_other!(*, a, b) });
impl_op_ex_commutative!(* |a: &Rational, b: &u16| -> Rational { op_other!(*, a, b) });
impl_op_ex_commutative!(* |a: &Rational, b: &i32| -> Rational { op_other!(*, a, b) });
impl_op_ex_commutative!(* |a: &Rational, b: &u32| -> Rational { op_other!(*, a, b) });
impl_op_ex_commutative!(* |a: &Rational, b: &i64| -> Rational { op_other!(*, a, b) });
impl_op_ex_commutative!(* |a: &Rational, b: &u64| -> Rational { op_other!(*, a, b) });
impl_op_ex_commutative!(* |a: &Rational, b: &isize| -> Rational { op_other!(*, a, b) });
impl_op_ex_commutative!(* |a: &Rational, b: &usize| -> Rational { op_other!(*, a, b) });
impl_op_ex_commutative!(* |a: &Rational, b: &Int| -> Rational { op_other!(*, a, b) });

// subtraction
impl_op_ex!(- |a: &Rational, b: &Rational| -> Rational { a + -b.clone() });
impl_op_ex!(- |a: &Rational, b: &i8| -> Rational { op_other!(-, a, b) });
impl_op_ex!(- |a: &Rational, b: &u8| -> Rational { op_other!(-, a, b) });
impl_op_ex!(- |a: &Rational, b: &i16| -> Rational { op_other!(-, a, b) });
impl_op_ex!(- |a: &Rational, b: &u16| -> Rational { op_other!(-, a, b) });
impl_op_ex!(- |a: &Rational, b: &i32| -> Rational { op_other!(-, a, b) });
impl_op_ex!(- |a: &Rational, b: &u32| -> Rational { op_other!(-, a, b) });
impl_op_ex!(- |a: &Rational, b: &i64| -> Rational { op_other!(-, a, b) });
impl_op_ex!(- |a: &Rational, b: &u64| -> Rational { op_other!(-, a, b) });
impl_op_ex!(- |a: &Rational, b: &isize| -> Rational { op_other!(-, a, b) });
impl_op_ex!(- |a: &Rational, b: &usize| -> Rational { op_other!(-, a, b) });
impl_op_ex!(- |a: &Rational, b: &Int| -> Rational { op_other!(-, a, b) });
impl_op_ex!(- |a: &i8, b: &Rational| -> Rational { op_other_reverse!(-, a, b) });
impl_op_ex!(- |a: &u8, b: &Rational| -> Rational { op_other_reverse!(-, a, b) });
impl_op_ex!(- |a: &i16, b: &Rational| -> Rational { op_other_reverse!(-, a, b) });
impl_op_ex!(- |a: &u16, b: &Rational| -> Rational { op_other_reverse!(-, a, b) });
impl_op_ex!(- |a: &i32, b: &Rational| -> Rational { op_other_reverse!(-, a, b) });
impl_op_ex!(- |a: &u32, b: &Rational| -> Rational { op_other_reverse!(-, a, b) });
impl_op_ex!(- |a: &i64, b: &Rational| -> Rational { op_other_reverse!(-, a, b) });
impl_op_ex!(- |a: &u64, b: &Rational| -> Rational { op_other_reverse!(-, a, b) });
impl_op_ex!(- |a: &isize, b: &Rational| -> Rational { op_other_reverse!(-, a, b) });
impl_op_ex!(- |a: &usize, b: &Rational| -> Rational { op_other_reverse!(-, a, b) });
impl_op_ex!(- |a: &Int, b: &Rational| -> Rational { op_other_reverse!(-, a, b) });

// division
impl_op_ex!(/ |a: &Rational, b: &Rational| -> Rational { a * b.reciprocal() });
impl_op_ex!(/ |a: &Rational, b: &i8| -> Rational { op_other!(/, a, b) });
impl_op_ex!(/ |a: &Rational, b: &u8| -> Rational { op_other!(/, a, b) });
impl_op_ex!(/ |a: &Rational, b: &i16| -> Rational { op_other!(/, a, b) });
impl_op_ex!(/ |a: &Rational, b: &u16| -> Rational { op_other!(/, a, b) });
impl_op_ex!(/ |a: &Rational, b: &i32| -> Rational { op_other!(/, a, b) });
impl_op_ex!(/ |a: &Rational, b: &u32| -> Rational { op_other!(/, a, b) });
impl_op_ex!(/ |a: &Rational, b: &i64| -> Rational { op_other!(/, a, b) });
impl_op_ex!(/ |a: &Rational, b: &u64| -> Rational { op_other!(/, a, b) });
impl_op_ex!(/ |a: &Rational, b: &isize| -> Rational { op_other!(/, a, b) });
impl_op_ex!(/ |a: &Rational, b: &usize| -> Rational { op_other!(/, a, b) });
impl_op_ex!(/ |a: &Rational, b: &Int| -> Rational { op_other!(/, a, b) });
impl_op_ex!(/ |a: &i8, b: &Rational| -> Rational { op_other_reverse!(/, a, b) });
impl_op_ex!(/ |a: &u8, b: &Rational| -> Rational { op_other_reverse!(/, a, b) });
impl_op_ex!(/ |a: &i16, b: &Rational| -> Rational { op_other_reverse!(/, a, b) });
impl_op_ex!(/ |a: &u16, b: &Rational| -> Rational { op_other_reverse!(/, a, b) });
impl_op_ex!(/ |a: &i32, b: &Rational| -> Rational { op_other_reverse!(/, a, b) });
impl_op_ex!(/ |a: &u32, b: &Rational| -> Rational { op_other_reverse!(/, a, b) });
impl_op_ex!(/ |a: &i64, b: &Rational| -> Rational { op_other_reverse!(/, a, b) });
impl_op_ex!(/ |a: &u64, b: &Rational| -> Rational { op_other_reverse!(/, a, b) });
impl_op_ex!(/ |a: &isize, b: &Rational| -> Rational { op_other_reverse!(/, a, b) });
impl_op_ex!(/ |a: &usize, b: &Rational| -> Rational { op_other_reverse!(/, a, b) });
impl_op_ex!(/ |a: &Int, b: &Rational| -> Rational { op_other_reverse!(/, a, b) });

//==========================================================

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    proptest! {
        #[test]
        fn test_abs(a: i64, b: i64) {
            prop_assert_eq!(Rational::new(a.abs(), b.abs()), Rational::new(a, b).abs());
        }

        #[test]
        fn test_floor(a: i64, b: i64) {
            prop_assume!(b != 0);
            let r = Rational::new(a, b);
            prop_assert!(Rational::from(r.floor()) <= r);
        }

        #[test]
        fn test_round(a: i64, b: i64) {
            prop_assume!(b != 0);
            let r = Rational::new(a.clone(), b.clone());
            let round = r.round();
            let lower = r.floor();
            let upper = r.floor() + 1;
            prop_assert!((&r - &round).abs() <= (&r - Rational::from(lower)).abs());
            prop_assert!((&r - round).abs() <= (r - Rational::from(upper)).abs());
        }
    }

    macro_rules! test_from_primitive {
        ($name:ident, $t:ty) => (
            #[test]
            fn $name() {
                let a = 23 as $t;
                let b = 35 as $t;
                let k = 3;
                let r = Rational { numer: Int::from(a), denom: Int::from(b) };
                assert_eq!(Rational::new(a, b), r);
                assert_eq!(Rational::from(a), Rational::new(a, 1));
                assert_eq!(Rational::new(k*a, k*b), r);
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

    #[test]
    fn test_from_int() {
        assert_eq!(Rational::from(Int::from(15)), Rational::new(15, 1));
    }

    #[test]
    fn test_new_with_string() {
        let a = "139485938475932340129348019238409128340918203498102394812";
        let b = "503948059384509384059380459380495830948503985039485";
        assert_eq!(Rational::new(a, b), Rational::new(a.to_int(), b.to_int()));
    }

    #[test]
    fn test_from_str() {
        let a = "12398429837498715129384791283749817234987123";
        let b = "698439892384958934859234859283498529348598932849582";
        assert_eq!(Rational::from_str(&format!("{}/{}", &a, &b)).unwrap(), Rational::new(a, b));
        assert_eq!(Rational::from_str(&format!("-{}/{}", &a, &b)).unwrap(), -Rational::new(a, b));
        assert_eq!(Rational::from_str(&format!("{}/-{}", &a, &b)).unwrap(), -Rational::new(a, b));
        assert_eq!(Rational::from_str(&format!("-{}/-{}", &a, &b)).unwrap(), Rational::new(a, b));
        assert_eq!(Rational::from_str(&format!("{} / {}", &a, &b)).unwrap(), Rational::new(a, b));
        assert_eq!(Rational::from_str(&format!("-{} / {}", &a, &b)).unwrap(), -Rational::new(a, b));
        assert_eq!(Rational::from_str(&format!("{} / -{}", &a, &b)).unwrap(), -Rational::new(a, b));
        assert_eq!(Rational::from_str(&format!("-{} / -{}", &a, &b)).unwrap(), Rational::new(a, b));
    }

    #[test]
    fn test_display() {
        assert_eq!(format!("{}", Rational::new(15, 10)), "3/2");
        assert_eq!(format!("{}", Rational::new(-15, 10)), "-3/2");
        assert_eq!(format!("{}", Rational::new(15, -10)), "-3/2");
        assert_eq!(format!("{}", Rational::new(-15, -10)), "3/2");
        assert_eq!(format!("{}", Rational::new(15, 5)), "3");
        assert_eq!(format!("{}", Rational::new(-15, 5)), "-3");
        assert_eq!(format!("{}", Rational::new(15, -5)), "-3");
        assert_eq!(format!("{}", Rational::new(-15, -5)), "3");
    }

    macro_rules! test_operations {
        ($name:ident, $t:ty) => (
            #[test]
            fn $name() {
                let a = Rational::new(1, 6);
                let b = Rational::new(-4, 3);
                let c = 8 as $t;

                assert_eq!(&a + &b, Rational::new(-7, 6));
                assert_eq!(&a + &b, &b + &a);
                assert_eq!(&a + &c, Rational::new(49, 6));
                assert_eq!(&a + &c, &c + &a);
                assert_eq!(&(&a + 0), &a);

                assert_eq!(&a * &b, Rational::new(-2, 9));
                assert_eq!(&a * &b, &b * &a);
                assert_eq!(&a * &c, Rational::new(4, 3));
                assert_eq!(&a * &c, &c * &a);
                assert_eq!(&a * 0, Rational::new(0, 1));
                assert_eq!(&(&a * 1), &a);
                assert_eq!(&(&a * -1), &-a.clone());

                assert_eq!(&a - &b, Rational::new(3, 2));
                assert_eq!(&a - &b, -(&b - &a));
                assert_eq!(&a - &c, Rational::new(-47, 6));
                assert_eq!(&a - &c, -(&c - &a));
                assert_eq!(&(&a - 0), &a);
                assert_eq!(&(0 - &a), &-a.clone());

                assert_eq!(&a / &b, Rational::new(-1, 8));
                assert_eq!(&a / &b, (&b / &a).reciprocal());
                assert_eq!(&a / &c, Rational::new(1, 48));
                assert_eq!(&a / &c, (&c / &a).reciprocal());
                assert_eq!((0 / &a), Rational::from(0));
                assert_eq!(&(&a / 1), &a);
                assert_eq!(&(&a / -1), &-a.clone());
                assert_eq!(&(1 / &a), &a.reciprocal());
                assert_eq!(&(-1 / &a), &-a.reciprocal());
            }
        )
    }
    test_operations!(test_operations_for_i8, i8);
    test_operations!(test_operations_for_u8, u8);
    test_operations!(test_operations_for_i16, i16);
    test_operations!(test_operations_for_u16, u16);
    test_operations!(test_operations_for_i32, i32);
    test_operations!(test_operations_for_u32, u32);
    test_operations!(test_operations_for_i64, i64);
    test_operations!(test_operations_for_u64, u64);
    test_operations!(test_operations_for_isize, isize);
    test_operations!(test_operations_for_usize, usize);

    proptest! {
        #[test]
        fn test_operations_with_int(a: i64, b: i64, c: i64) {
            prop_assume!(a != 0 && b != 0 && c != 0);
            let r = Rational::new(a, b);
            let c_int = Int::from(c.clone());
            let c_rational = Rational::from(c);
            prop_assert_eq!(&r + &c_int, &r + &c_rational);
            prop_assert_eq!(&r * &c_int, &r * &c_rational);
            prop_assert_eq!(&r - &c_int, &r - &c_rational);
            prop_assert_eq!(&r / &c_int, &r / &c_rational);
        }
    }
}

