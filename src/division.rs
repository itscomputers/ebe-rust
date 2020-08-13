use crate::types::int::{Int, ToInt};

//----------------------------
// division with remainder

#[derive(Debug)]
pub struct DivRem {
    pub quotient: Int,
    pub remainder: Int
}

pub fn div_rem<T: ToInt, U: ToInt>(a: &T, b: &U) -> DivRem {
    let a = a.to_int();
    let b = b.to_int();
    let remainder = if a.is_negative() {
        &a % &b + b.abs()
    } else {
        &a % &b
    };
    let quotient = (a - &remainder) / b;

    DivRem { quotient, remainder }
}

pub fn div<T: ToInt, U: ToInt>(a: &T, b: &U) -> Int {
    div_rem(a, b).quotient
}

pub fn rem<T: ToInt, U: ToInt>(a: &T, b: &U) -> Int {
    div_rem(a, b).remainder
}

//----------------------------
// gcd and lcm

pub fn gcd<T: ToInt, U: ToInt>(a: &T, b: &U) -> Int {
    match (&a.to_int(), &b.to_int()) {
        (a, b) if a.is_zero() && b.is_zero() => panic!("gcd(0, 0) is undefined"),
        (a, b) if b.is_zero() => a.abs(),
        _ => gcd(b, &rem(a, b))
    }
}

macro_rules! gcd {
    ($($arg:expr),*) => {{
        let mut temp_gcd = Int::from(1);
        $({
            temp_gcd = gcd(&temp_gcd, $arg);
        })*
        temp_gcd
    }};
}

pub fn lcm<T: ToInt, U: ToInt>(a: &T, b: &U) -> Int {
    match (&a.to_int(), &b.to_int()) {
        (a, b) if a.is_zero() => panic!("lcm(0, {}) is undefined", b),
        (a, b) if b.is_zero() => panic!("lcm({}, 0) is undefined", a),
        (a, b) => ((a / gcd(a, b)) * b).abs(),
    }
}

macro_rules! lcm {
    ($($arg:expr),*) => {{
        let mut temp_lcm = Int::from(1);
        $({
            temp_lcm = lcm(&temp_lcm, $arg);
        })*
        temp_lcm
    }};
}

//----------------------------
// bezout

#[derive(Debug)]
pub struct BezoutSolution {
    pub x: Int,
    pub y: Int
}

fn next_bezout_solution(quotient: Int, prev: BezoutSolution, curr: &BezoutSolution) -> BezoutSolution {
    let x = prev.x - &curr.x * &quotient;
    let y = prev.y - &curr.y * quotient;
    BezoutSolution { x, y }
}

fn bezout_recursive(a: Int, b: Int, prev: BezoutSolution, curr: BezoutSolution) -> BezoutSolution {
    match (&a, &b) {
        (a, b) if b.is_zero() && a.is_negative() => BezoutSolution { x: -prev.x, y: -prev.y },
        (_, b) if b.is_zero() => prev,
        _ => {
            let d = div_rem(&a, &b);
            let next = next_bezout_solution(d.quotient, prev, &curr);
            bezout_recursive(b, d.remainder, curr, next)
        }
    }
}

pub fn bezout<T: ToInt, U: ToInt>(a: &T, b: &U) -> BezoutSolution {
    match (&a.to_int(), &b.to_int()) {
        (a, b) if a.is_zero() && b.is_zero() => panic!("gcd(0, 0) is undefined"),
        (a, b) => {
            let prev = BezoutSolution { x: Int::from(1), y: Int::from(0) };
            let curr = BezoutSolution { x: Int::from(0), y: Int::from(1) };
            bezout_recursive(a.clone(), b.clone(), prev, curr)
        }
    }
}

//==========================================================

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    proptest! {
        #[test]
        fn test_div_rem_props(a: i64, b: i64) {
            prop_assume!(b != 0);
            let d = div_rem(&a, &b);
            prop_assert!(d.remainder.is_positive() || d.remainder.is_zero());
            prop_assert!(d.remainder < Int::from(b).abs());
            prop_assert_eq!(d.quotient*b + d.remainder, Int::from(a));
        }

        #[test]
        fn test_gcd_props(a: i64, b: i64) {
            prop_assume!(a != 0 || b != 0);
            let d = gcd(&a, &b);
            prop_assert!(d.is_positive());
            prop_assert!((Int::from(a) % &d).is_zero());
            prop_assert!((Int::from(b) % &d).is_zero());

            let reduced_a = a / &d;
            let reduced_b = b / d;
            prop_assert_eq!(gcd(&reduced_a, &reduced_b), Int::from(1));
        }

        #[test]
        fn test_gcd_multiple(a: i64, b: i64, c: i64) {
            prop_assume!(a != 0 || b != 0 || c != 0);
            let d = gcd!(&a, &b, &c);
            prop_assert!(d.is_positive());
            prop_assert!((Int::from(a) % &d).is_zero());
            prop_assert!((Int::from(b) % &d).is_zero());
            prop_assert!((Int::from(c) % &d).is_zero());
            let reduced_a = a / &d;
            let reduced_b = b / &d;
            let reduced_c = c / d;
            prop_assert_eq!(gcd!(&reduced_a, &reduced_b, &reduced_c), Int::from(1));
        }

        #[test]
        fn test_lcm_props(a: i64, b: i64) {
            prop_assume!(a != 0 && b != 0);
            let m = lcm(&a, &b);
            prop_assert!(m.is_positive());
            prop_assert!((&m % &a).is_zero());
            prop_assert!((&m % &b).is_zero());

            let reduced_a = &m / &a;
            let reduced_b = m / &b;
            prop_assert_eq!(gcd(&reduced_a, &reduced_b), Int::from(1));
        }

        #[test]
        fn test_lcm_multiple(a: i64, b: i64, c: i64) {
            prop_assume!(a != 0 && b != 0 && c != 0);
            let m = lcm!(&a, &b, &c);
            prop_assert!(m.is_positive());
            prop_assert!((&m % Int::from(a)).is_zero());
            prop_assert!((&m % Int::from(b)).is_zero());
            prop_assert!((&m % Int::from(c)).is_zero());
            let reduced_a = &m / a;
            let reduced_b = &m / b;
            let reduced_c = m / c;
            prop_assert_eq!(gcd!(&reduced_a, &reduced_b, &reduced_c), Int::from(1));
        }

        #[test]
        fn test_bezout(a: i64, b: i64) {
            prop_assume!(a != 0 || b != 0);
            prop_assert!(bezout_value_eq_gcd(a, b));
        }
    }

    fn bezout_value_eq_gcd(a: i64, b: i64) -> bool {
        let solution = bezout(&a, &b);
        let bezout_value = &a*solution.x + &b*solution.y;
        let gcd_value = gcd(&a, &b);
        bezout_value == gcd_value
    }

    #[test]
    fn test_bezout_explicit() {
        assert!(bezout_value_eq_gcd(-15, -3));
        assert!(bezout_value_eq_gcd(10, -2));
    }

    #[test]
    #[should_panic(expected="gcd(0, 0) is undefined")]
    fn test_gcd_zeroes() {
        gcd(&Int::from(0), &Int::from(0));
    }

    #[test]
    #[should_panic(expected="lcm(0, 5) is undefined")]
    fn test_lcm_first_zero() {
        lcm(&Int::from(0), &Int::from(5));
    }

    #[test]
    #[should_panic(expected="lcm(5, 0) is undefined")]
    fn test_lcm_second_zero() {
        lcm(&Int::from(5), &Int::from(0));
    }
}
