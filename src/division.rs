pub fn div_rem(a: i64, b: i64) -> (i64, i64) {
    let remainder = if a < 0 {
        a % b + i64::abs(b)
    } else {
        a % b
    };
    let quotient = (a - remainder) / b;

    (quotient, remainder)
}

pub fn euclidean_algorithm(a: i64, b: i64) -> String {
    if b == 0 {
        return String::from("");
    }

    let (q, r) = div_rem(a, b);
    let equation = format!("{} == {} * {} + {}", a, b, q, r);

    format!("{}\n{}", equation, euclidean_algorithm(b, r))
}

pub fn gcd(a: i64, b: i64) -> i64 {
    match (a, b) {
        (0, 0) => panic!("gcd(0, 0) is undefined"),
        (x, 0) => i64::abs(x),
        _ => gcd(b, a % b)
    }
}

fn bezout_helper(a: i64, b: i64, prev: (i64, i64), curr: (i64, i64)) -> (i64, i64) {
    if b == 0 {
        return prev;
    }
    let (q, r) = div_rem(a, b);
    let x = prev.0 - curr.0 * q;
    let y = prev.1 - curr.1 * q;

    bezout_helper(b, r, curr, (x, y))
}

pub fn bezout(a: i64, b: i64) -> (i64, i64) {
    match (a, b) {
        (0, 0) => panic!("gcd(0, 0) is undefined"),
        (a, 0) => (i64::signum(a), 0),
        _ => {
            match div_rem(a, b) {
                (_q, 0) => (0, i64::signum(b)),
                (q, r) => bezout_helper(b, r, (0, 1), (1, -q))
            }
        }
    }
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
            let (q, r) = div_rem(a, b);
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
        fn test_bezout(a: i32, b: i32) {
            prop_assume!(a != 0 || b != 0);
            let a = a as i64;
            let b = b as i64;
            let (x, y) = bezout(a, b);
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

    fn bezout_value(a: i64, b: i64) -> i64 {
        let (x, y) = bezout(a, b);
        a*x + b*y
    }

    #[test]
    fn test_bezout_explicit() {
        assert_eq!(bezout_value(-15, -3), gcd(15, 3));
        assert_eq!(bezout_value(10, -2), gcd(10, 2));
    }

    #[test]
    fn test_euclidean_algorithm() {
        let s = "322 == 70 * 4 + 42\n70 == 42 * 1 + 28\n42 == 28 * 1 + 14\n28 == 14 * 2 + 0\n";
        assert_eq!(euclidean_algorithm(322, 70).as_str(), s);
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
