use std::{fmt, ops};
use std::cmp::Ordering;
use std::num::ParseIntError;
use std::str::FromStr;

use crate::int::Int;
use crate::division::gcd;

#[derive(Debug, Clone)]
struct Rational {
    numer: Int,
    denom: Int,
}

impl fmt::Display for Rational {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}/{}", self.numer, self.denom)
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

// initialization

impl Rational {
    pub fn new(numer: Int, denom: Int) -> Rational {
        if denom.is_zero() { panic!("{}/0 is undefined", numer); }

        let d = gcd(&numer, &denom);
        match (numer / &d, denom / &d) {
            (a, _b) if a.is_zero() => Rational { numer: a, denom: Int::from(1) },
            (a, b) if b.is_negative() => Rational { numer: -a, denom: -b },
            (a, b) => Rational { numer: a, denom: b },
        }
    }
}

impl From<[i32; 2]> for Rational {
    fn from(inputs: [i32; 2]) -> Self {
        let [numer, denom] = inputs;
        Self::new(Int::from(numer), Int::from(denom))
    }
}

impl From<[i64; 2]> for Rational {
    fn from(inputs: [i64; 2]) -> Self {
        let [numer, denom] = inputs;
        Self::new(Int::from(numer), Int::from(denom))
    }
}

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

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    fn test_new_works_for(numer: i32, denom: i32) {
        let numer = Int::from(numer);
        let denom = Int::from(denom);
        let rational = Rational::new(numer.clone(), denom.clone());
        assert_eq!(Rational { numer, denom }, rational);
        assert!(rational.denom.is_positive());
        assert_eq!(gcd(&rational.numer, &rational.denom), Int::from(1));
    }

    #[test]
    fn test_new() {
        test_new_works_for(12, 15);
        test_new_works_for(-12, 15);
        test_new_works_for(12, -15);
        test_new_works_for(-12, -15);
    }

    #[test]
    fn test_from_i32() {
        let numer: i32 = 123;
        let denom: i32 = 456;
        assert_eq!(
            Rational::from([numer, denom]),
            Rational::new(Int::from(numer), Int::from(denom))
        );
    }

    #[test]
    fn test_from_i64() {
        let numer: i64 = 123;
        let denom: i64 = 456;
        assert_eq!(
            Rational::from([numer, denom]),
            Rational::new(Int::from(numer), Int::from(denom))
        );
    }

    #[test]
    fn test_from_str() {
        assert_eq!(Rational::from_str("15/10").unwrap(), Rational::from([3, 2]));
        assert_eq!(Rational::from_str("15/-10").unwrap(), Rational::from([3, -2]));
        assert_eq!(Rational::from_str("-15/10").unwrap(), Rational::from([-3, 2]));
        assert_eq!(Rational::from_str("-15/-10").unwrap(), Rational::from([-3, -2]));
        assert_eq!(Rational::from_str("15 / 10").unwrap(), Rational::from([3, 2]));
        assert_eq!(Rational::from_str("15 / -10").unwrap(), Rational::from([3, -2]));
        assert_eq!(Rational::from_str("-15 / 10").unwrap(), Rational::from([-3, 2]));
        assert_eq!(Rational::from_str("-15 / -10").unwrap(), Rational::from([-3, -2]));
    }

    #[test]
    fn test_display() {
        assert_eq!(format!("{}", Rational::from([15, 10])), "3/2");
        assert_eq!(format!("{}", Rational::from([-15, 10])), "-3/2");
        assert_eq!(format!("{}", Rational::from([15, -10])), "-3/2");
        assert_eq!(format!("{}", Rational::from([-15, -10])), "3/2");
    }
}

