use crate::int::Int;

pub fn div_rem(a: &Int, b: &Int) -> (Int, Int) {
    let remainder = if a.is_negative() {
        a % b + b.abs()
    } else {
        a % b
    };
    let quotient = (a - &remainder) / b;

    (quotient, remainder)
}

pub fn div(a: &Int, b: &Int) -> Int {
    div_rem(a, b).0
}

pub fn rem(a: &Int, b: &Int) -> Int {
    div_rem(a, b).1
}

pub fn euclidean_algorithm(a: Int, b: Int) -> String {
    if b.is_zero() {
        return String::from("");
    }

    let (q, r) = div_rem(&a, &b);
    let equation = format!("{} == {} * {} + {}", a, b, q, r);

    format!("{}\n{}", equation, euclidean_algorithm(b, r))
}

pub fn gcd(a: &Int, b: &Int) -> Int {
    match (a, b) {
        (a, b) if a.is_zero() && b.is_zero() => panic!("gcd(0, 0) is undefined"),
        (a, b) if b.is_zero() => a.abs(),
        _ => gcd(&b, &(a % b))
    }
}

fn bezout_helper(a: &Int, b: &Int, prev: (Int, Int), curr: (Int, Int)) -> (Int, Int) {
    if b.is_zero() {
        return prev;
    }
    let (q, r) = div_rem(a, b);
    let x = prev.0 - &curr.0 * &q;
    let y = prev.1 - &curr.1 * q;

    bezout_helper(b, &r, curr, (x, y))
}

pub fn bezout(a: &Int, b: &Int) -> (Int, Int) {
    match (a, b) {
        (a, b) if a.is_zero() && b.is_zero() => panic!("gcd(0, 0) is undefined"),
        (a, b) if b.is_zero() => (Int::from(a.signum()), Int::from(0)),
        _ => {
            match div_rem(a, b) {
                (_q, r) if r.is_zero() => (Int::from(0), Int::from(b.signum())),
                (q, r) => bezout_helper(b, &r, (Int::from(0), Int::from(1)), (Int::from(1), -q)),
            }
        }
    }
}

pub fn lcm(a: &Int, b: &Int) -> Int {
    match (a, b) {
        (a, b) if a.is_zero() => panic!("lcm(0, {}) is undefined", b),
        (a, b) if b.is_zero() => panic!("lcm({}, 0) is undefined", a),
        _ => ((a / gcd(a, b)) * b).abs(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    proptest! {
        #[test]
        fn test_div_rem_props(a: i64, b: i64) {
            let a = Int::from(a);
            let b = Int::from(b);
            prop_assume!(b.is_nonzero());
            let (q, r) = div_rem(&a, &b);
            prop_assert!(r.is_positive() || r.is_zero());
            prop_assert!(r < b.abs());
            prop_assert_eq!(q*b + r, a);
        }

        #[test]
        fn test_gcd_props(a: i64, b: i64) {
            let a = Int::from(a);
            let b = Int::from(b);
            prop_assume!(a.is_nonzero() || b.is_nonzero());
            let d = gcd(&a, &b);
            prop_assert!(d.is_positive());
            prop_assert!((&a % &d).is_zero());
            prop_assert!((&b % &d).is_zero());
            prop_assert_eq!(gcd(&(&a/&d), &(b/d)), Int::from(1));
        }

        #[test]
        fn test_bezout(a: i64, b: i64) {
            let a = Int::from(a);
            let b = Int::from(b);
            prop_assume!(a.is_nonzero() || b.is_nonzero());
            let (x, y) = bezout(&a, &b);
            prop_assert_eq!(&a*x + &b*y, gcd(&a, &b));
        }

        #[test]
        fn test_lcm_props(a: i64, b: i64) {
            let a = Int::from(a);
            let b = Int::from(b);
            prop_assume!(a.is_nonzero() && b.is_nonzero());
            let d = gcd(&a, &b);
            let m = lcm(&a, &b);
            prop_assert!(m.is_positive());
            prop_assert!((&m % &a).is_zero());
            prop_assert!((m % &b).is_zero());
            prop_assert_eq!(lcm(&(&a/&d), &(&b/&d)), ((a/&d)*(b/d)).abs());
        }
    }

    fn bezout_value_eq_gcd(a: i32, b: i32) -> bool {
        let a = Int::from(a);
        let b = Int::from(b);
        let (x, y) = bezout(&a, &b);
        let bezout_value = &a*x + &b*y;
        let gcd_value = gcd(&a, &b);
        bezout_value == gcd_value
    }

    #[test]
    fn test_bezout_explicit() {
        assert!(bezout_value_eq_gcd(-15, -3));
        assert!(bezout_value_eq_gcd(10, -2));
    }

    #[test]
    fn test_euclidean_algorithm() {
        let s = "322 == 70 * 4 + 42\n70 == 42 * 1 + 28\n42 == 28 * 1 + 14\n28 == 14 * 2 + 0\n";
        assert_eq!(euclidean_algorithm(Int::from(322), Int::from(70)).as_str(), s);
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
