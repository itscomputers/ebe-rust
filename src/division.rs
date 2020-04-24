use std::cmp;

pub fn div_rem(a: i64, b: i64) -> [i64; 2] {
    let remainder = if a < 0 {
        a % b + i64::abs(b)
    } else {
        a % b
    };
    let quotient = (a - remainder) / b;

    [quotient, remainder]
}

fn gcd_naive(a: i64, b: i64) -> i64 {
    let mut divisor: i64 = 1;

    let upper = cmp::max(i64::abs(a), i64::abs(b));
    for d in 2..upper+1 {
        if a % d == 0 && b % d == 0 {
            divisor = d;
        }
    }

    divisor
}

pub fn gcd(a: i64, b: i64) -> i64 {
    match (a, b) {
        (0, 0) => panic!("gcd(0, 0) is undefined"),
        (x, 0) => i64::abs(x),
        _ => gcd(b, a % b)
    }
}

fn bezout_helper(a: i64, b: i64, prev: [i64; 2], curr: [i64; 2]) -> [i64; 2] {
    if b == 0 {
        return prev;
    }
    let [q, r] = div_rem(a, b);
    let x = prev[0] - curr[0] * q;
    let y = prev[1] - curr[1] * q;

    bezout_helper(b, r, curr, [x, y])
}

pub fn bezout(a: i64, b: i64) -> [i64; 2] {
    let [mut x, mut y] = bezout_helper(i64::abs(a), i64::abs(b), [1, 0], [0, 1]);
    if a < 0 { x *= -1 };
    if b < 0 { y *= -1} ;
    [x, y]
}

pub fn lcm(a: i64, b: i64) -> i64 {
    match (a, b) {
        (0, x) => panic!("lcm(0, {}) is undefined", x),
        (x, 0) => panic!("lcm({}, 0) is undefined", x),
        _ => i64::abs((a / gcd(a, b)) * b)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    proptest! {
        #[test]
        fn test_div_rem_props(a: i32, b: i32) {
            let a = a as i64;
            let b = b as i64;
            prop_assume!(b != 0);
            let [q, r] = div_rem(a, b);
            prop_assert!(0 <= r);
            prop_assert!(r < i64::abs(b));
            prop_assert_eq!(q*b + r, a);
        }

        #[test]
        fn test_gcd_props(a: i64, b: i64) {
            prop_assume!(a != 0 || b != 0);
            let d = gcd(a, b);
            prop_assert!(d > 0);
            prop_assert_eq!(a % d, 0);
            prop_assert_eq!(b % d, 0);
            prop_assert_eq!(gcd(a/d, b/d), 1);
        }

        #[test]
        fn test_gcd_against_naive(a in 1i64..1000, b in 1i64..1000) {
            prop_assert_eq!(gcd_naive(a, b), gcd(a, b));
        }

        #[test]
        fn test_bezout(a: i32, b: i32) {
            prop_assume!(a != 0 || b != 0);
            let a = a as i64;
            let b = b as i64;
            let [x, y] = bezout(a, b);
            prop_assert_eq!(a*x + b*y, gcd(a, b));
        }

        #[test]
        fn test_lcm_props(a: i32, b: i32) {
            prop_assume!(a != 0 && b != 0);
            let a = a as i64;
            let b = b as i64;
            let d = gcd(a, b);
            let m = lcm(a, b);
            prop_assert!(m > 0);
            prop_assert!(m % a == 0);
            prop_assert!(m % b == 0);
            prop_assert_eq!(lcm(a/d, b/d), i64::abs((a/d)*(b/d)));
        }
    }

    #[test]
    #[should_panic(expected="gcd(0, 0) is undefined")]
    fn test_gcd_zeroes() {
        gcd(0, 0);
    }

    #[test]
    #[should_panic(expected="lcm(0, 5) is undefined")]
    fn test_lcm_first_zero() {
        lcm(0, 5);
    }

    #[test]
    #[should_panic(expected="lcm(5, 0) is undefined")]
    fn test_lcm_second_zero() {
        lcm(5, 0);
    }
}
