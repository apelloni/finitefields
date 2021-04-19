extern crate libc;
use libc::c_ulong;
use std::fmt;
use std::fmt::{Display, Formatter};
use std::ops::Neg;
use std::ops::{Add, AddAssign, Div, Mul, MulAssign, Sub, SubAssign};

extern crate serde;
use serde::{Deserialize, Serialize};

pub type FF = u64;

pub mod primes;

extern "C" {
    /// Fast multiplication using C
    pub fn mul_mod(a: c_ulong, b: c_ulong, m: c_ulong) -> c_ulong;
}

/// Allows to perform simple algebraic operations over a finite field
///
/// # Arguments
///
/// * `value` - number be represented as `value % modulo`
/// * `modulo` - An integer corresponding to the size of the modular space.
///  For this to be a finite field it must be a **prime number**!
///
///
/// # Examples
///
/// ```
/// // Simple operations within a finite field
///
/// use finitefields::{FF,Finitefield,primes};
///
/// fn main(){
///     // Pick a prime
///     let modulo = primes::PRIMES31[0];
///     // Define numbers to be cast into our field
///     let num1: FF = 23742687;
///     let num2: FF = 87129774;
///       
///     let fnum1 = Finitefield::new(num1, modulo).unwrap();
///     let fnum2 = Finitefield::new(num2, modulo).unwrap();
///     
///     // Compute product
///     let product = fnum1 * fnum2;
///     assert_eq!(product.value, 174523906);
///
///     // Compute the inverse of the product
///     let product_inv = product.inverse().unwrap();
///     assert_eq!(product_inv.value, 486606559);
///
///     // Multiply by the product
///     assert_eq!((product * product_inv).value, 1);
/// }
/// ```
#[derive(Debug, Copy, Deserialize, Serialize)]
pub struct Finitefield {
    pub value: FF,
    pub modulo: FF,
}

impl Clone for Finitefield {
    #[inline]
    fn clone(&self) -> Finitefield {
        *self
    }
}

impl Display for Finitefield {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "{}", self.value)
    }
}

impl AddAssign for Finitefield {
    fn add_assign(&mut self, rhs: Finitefield) {
        self.value = (*self + rhs).value;
    }
}

impl MulAssign for Finitefield {
    fn mul_assign(&mut self, rhs: Finitefield) {
        self.value = (*self * rhs).value;
    }
}

impl Add<Finitefield> for Finitefield {
    type Output = Finitefield;

    #[inline]
    fn add(self, other: Finitefield) -> Finitefield {
        assert_eq!(
            self.modulo, other.modulo,
            "Trying to sum two Finitefields with different modula"
        );
        Finitefield {
            value: (self.value + other.value) % self.modulo,
            modulo: self.modulo,
        }
    }
}

impl Add<FF> for Finitefield {
    type Output = Finitefield;

    #[inline]
    fn add(self, other: FF) -> Finitefield {
        Finitefield {
            value: (self.value + other) % self.modulo,
            modulo: self.modulo,
        }
    }
}

impl Sub for Finitefield {
    type Output = Finitefield;

    #[inline]
    fn sub(self, other: Finitefield) -> Finitefield {
        assert_eq!(
            self.modulo, other.modulo,
            "Trying to subtract two Finitefields with different modula"
        );
        Finitefield {
            value: (self.value + (self.modulo - other.value)) % self.modulo,
            modulo: self.modulo,
        }
    }
}

impl Sub<FF> for Finitefield {
    type Output = Finitefield;

    #[inline]
    fn sub(self, other: FF) -> Finitefield {
        Finitefield {
            value: (self.value + (self.modulo - other)) % self.modulo,
            modulo: self.modulo,
        }
    }
}

impl SubAssign for Finitefield {
    fn sub_assign(&mut self, rhs: Finitefield) {
        self.value = (*self - rhs).value;
    }
}

impl Mul for Finitefield {
    type Output = Finitefield;

    #[inline]
    fn mul(self, other: Finitefield) -> Finitefield {
        assert_eq!(
            self.modulo, other.modulo,
            "Trying to multiply two Finitefields with different modula"
        );
        Finitefield {
            value: Finitefield::mod_multiply(self.value, other.value, self.modulo),
            modulo: self.modulo,
        }
    }
}

impl Mul<FF> for Finitefield {
    type Output = Finitefield;

    #[inline]
    fn mul(self, other: FF) -> Finitefield {
        Finitefield {
            value: (self.value * other) % self.modulo,
            modulo: self.modulo,
        }
    }
}

impl Div for Finitefield {
    type Output = Finitefield;

    #[inline]
    fn div(self, other: Finitefield) -> Finitefield {
        assert_eq!(
            self.modulo, other.modulo,
            "Trying to divide two Finitefields with different modula"
        );

        self * other.inverse().unwrap()
        //Finitefield {
        //    value: (self.value * other.inverse().unwrap().value) % self.modulo,
        //    modulo: self.modulo,
        //}
    }
}

impl Neg for Finitefield {
    type Output = Finitefield;

    #[inline]
    fn neg(self) -> Finitefield {
        Finitefield {
            value: (self.modulo - self.value) % self.modulo,
            modulo: self.modulo,
        }
    }
}

impl Finitefield {
    #[inline]
    pub fn new(value: FF, modulo: FF) -> Result<Finitefield, &'static str> {
        assert!(
            modulo < 9223372036854775807,
            "Module must be a prime smaller than 9,223,372,036,854,775,807 size"
        );
        Ok(Finitefield {
            value: value % modulo,
            modulo: modulo,
        })
    }

    #[inline]
    pub fn zero(modulo: FF) -> Finitefield {
        Finitefield {
            value: 0,
            modulo: modulo,
        }
    }

    #[inline]
    pub fn one(modulo: FF) -> Finitefield {
        Finitefield {
            value: 1,
            modulo: modulo,
        }
    }

    #[inline]
    pub fn is_zero(&self) -> bool {
        self.value == 0
    }

    #[inline]
    pub fn update(&mut self, value: FF) {
        self.value = value % self.modulo;
    }

    /// Implementation of the multiplication of two positive integers a, b
    /// over a modulo.
    /// This multipication takes advantage of the x86 architecture, in particular
    /// is based on the way floats and integer discards overflowing digits.
    ///
    /// TODO: check if this will still work for ARM architecture
    #[inline]
    pub fn mod_multiply(a: FF, b: FF, modulo: FF) -> FF {
        // When the size of modulo is larger then 2^31-1 then we want to use the C
        // routing in order to compute the product of two numbers.
        if modulo < 2147483647 {
            let c: u64 = ((a as f64) * (b as f64) / (modulo as f64)) as u64;
            match FF::overflowing_sub(
                FF::overflowing_mul(a, b).0,
                FF::overflowing_mul(c, modulo).0,
            ) {
                (v, false) => v % modulo,
                (v, true) => FF::overflowing_add(modulo, v).0 % modulo,
            }
        } else {
            unsafe { mul_mod(a, b, modulo) }
        }
    }

    /// Extended Eucleadean Algorithm in terturn the GCD of two
    /// numbers `a` and `b` and two extra coefficients `x` and `y`:
    ///
    /// `gcd(a,b) = x * a + y * b`
    #[inline]
    pub fn egcd(&self, a: FF, b: FF) -> (FF, FF, FF) {
        if a > b {
            return self.egcd(b, a);
        }
        if a == 0 {
            return (b, 0, 1);
        } else {
            let (g, x, y) = self.egcd(b % a, a);
            // g = (b % a ) * x + y * a
            // b % a = b - b/a
            //let r = (b / a) * x;
            let r = match FF::overflowing_mul(b / a, x) {
                (v, false) => v,
                (_, true) => Finitefield::mod_multiply(b / a, x, self.modulo),
            };
            if r < y {
                return (g, y - r, x);
            } else {
                return (g, (y + self.modulo) - r % self.modulo, x);
            }
        }
    }

    /// Compute the inverse by means of the Extended Eucleadean Algorithm
    // ( see egcd() )
    #[inline]
    pub fn inverse(&self) -> Result<Finitefield, String> {
        let (g, x, _) = self.egcd(self.value, self.modulo);
        if g != 1 {
            return Err(format!(
                "The number {0} is not invertible in mod {1}!",
                self.value, self.modulo
            ));
        } else {
            Ok(Finitefield {
                value: x % self.modulo,
                modulo: self.modulo,
            })
        }
    }

    /// Compute the exponent of the value over the finite field
    #[inline]
    pub fn pow(&self, mut exp: usize) -> Finitefield {
        if exp == 0 {
            return Finitefield::one(self.modulo);
        }
        let mut base = self.clone();

        while exp & 1 == 0 {
            base = base.clone() * base;
            exp >>= 1;
        }
        if exp == 1 {
            return base;
        }

        let mut acc = base.clone();
        while exp > 1 {
            exp >>= 1;
            base = base.clone() * base;
            if exp & 1 == 1 {
                acc = acc * base.clone();
            }
        }
        acc
    }
}

#[test]
pub fn test() {
    use std::time::{Duration, Instant}; // Binary operations //Uniary operations
                                        // Check arbitrary prime
    let module = 323780508946331;
    let mut n1 = Finitefield::new(9213372036845593434, module).unwrap();
    let n2 = Finitefield::new(9123371590535809495, module).unwrap();
    unsafe {
        mul_mod(n1.value, n2.value, module);
    }
    let product = n1 * n2;
    let ratio12 = n1 / n2;
    let ratio21 = n2 / n1;
    assert_eq!(product.value, 260026117358415);
    assert_eq!(ratio12.value, 32274628318948);
    assert_eq!(ratio21.value, 50068043648017);

    n1 = n1 + 2;
    let product = n1 * n2;
    let ratio12 = n1 / n2;
    let ratio21 = n2 / n1;
    assert_eq!(product.value, 28845009547569);
    assert_eq!(ratio12.value, 316935518309367);
    assert_eq!(ratio21.value, 5934096782165);

    // Check for largest possible prime number
    let module = 9223372036854775643;
    let n1 = Finitefield::new(9213372036845593436, module).unwrap();
    let n2 = Finitefield::new(9123371590535809495, module).unwrap();
    let summing = n1 + n2;
    let subtract = n1 - n2;
    let product = n1 * n2;
    let ratio12 = n1 / n2;
    let ratio21 = n2 / n1;
    let inverse1 = n1.inverse().unwrap();
    let inverse2 = n2.inverse().unwrap();

    assert_eq!(summing.value, 9113371590526627288, "Test sum");
    assert_eq!(subtract.value, 90000446309783941, "Test subtraction",);
    assert_eq!(product.value, 2735553790181227265, "Test product");
    assert_eq!(ratio12.value, 4527033544546678236, "Test ration12");
    assert_eq!(ratio21.value, 3666964563492791022, "Test ration21");
    assert_eq!(inverse1.value, 5827441276739351168, "Test inverse1");
    assert_eq!(inverse2.value, 7895880808225951134, "Test inverse 2");

    //TEST speed
    let mut now = Instant::now();
    for i in 0..(1e7 as usize) {
        let m = 323780508946331;
        //let n1: u64 = 9213372036845593434 + (i as u64) % m;
        let n1: u64 = (9213372036845593434 + (i as u64)) % m;
        let n2: u64 = 9123371590535809495 % m;
        //let c: u64 = ((n1 as f64) * (n2 as f64) / (m as f64)) as u64;
        //let r1 = (u64::overflowing_mul(n1, n2).0 - u64::overflowing_mul(c, m).0) % m;
        let r2 = Finitefield::mod_multiply(n1, n2, m);
        //assert_eq!(r1, r2, "{} ::  {} * {}", (i as u64), n1, n2);
    }
    println!("LARGE rust\t(x 1e7) => {:?}", now.elapsed());

    let mut now = Instant::now();
    for i in 0..(1e7 as usize) {
        let m = 323780508946331;
        let n1: u64 = (9213372036845593434 + (i as u64)) % m;
        let n2: u64 = 9123371590535809495 % m;
        let r1 = unsafe { mul_mod(n1, n2, m) };
    }
    println!("LARGE C \t(x 1e7) => {:?}", now.elapsed());

    now = Instant::now();
    for i in 0..(1e7 as usize) {
        let m: u64 = 2038074743;
        let n1: u64 = 130575468 % m;
        let n2: u64 = 1021486737 % m;
        let r1 = Finitefield::mod_multiply(n1, n2, m);
    }
    println!("SMALL rust\t(x 1e7) => {:?}", now.elapsed());

    now = Instant::now();
    for i in 0..(1e7 as usize) {
        let m: u64 = 2038074743;
        let n1: u64 = 130575468 % m;
        let n2: u64 = 1021486737 % m;
        let r1 = unsafe { mul_mod(n1, n2, m) };
    }
    println!("SMALL C \t(x 1e7) => {:?}", now.elapsed());

    now = Instant::now();
    for i in 0..(1e7 as usize) {
        let m: u64 = 2038074743;
        let n1: u64 = 130575468 % m;
        let n2: u64 = 1021486737 % m;
        let r1 = (n1 * n2) % m;
        Finitefield::mod_multiply(n1, n2, m);
    }
    println!("SMALL % mod\t(x 1e7) => {:?}", now.elapsed());

    now = Instant::now();
    //for i in 0..(1e9 as usize) {
    for i in 0..(1e7 as usize) {
        let m: u64 = 2038074743;
        let n1: u64 = (130575468 + (i as u64)) % m;
        let n2: u64 = (1021486737 + (i as u64)) % m;
        let r1 = (n1 * n2) % m;
        let r2 = Finitefield::mod_multiply(n1, n2, m);
        let r3 = unsafe { mul_mod(n1, n2, m) };
        assert_eq!(r1, r2);
        assert_eq!(r1, r3);
    }
    println!("SMALL COMPARE\t(x 1e9) => {:?}", now.elapsed());
}
