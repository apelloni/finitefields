# finitefields
[![crates.io](https://img.shields.io/crates/v/finitefields.svg)](https://crates.io/crates/finitefields)
[![documentation](https://docs.rs/finitefields/badge.svg)](https://docs.rs/finitefields)
[![Build Status](https://travis-ci.com/apelloni/finitefields.svg?branch=main)](https://travis-ci.com/apelloni/finitefields)
[![Byy Me A Coffee](https://www.buymeacoffee.com/assets/img/custom_images/orange_img.png)](https://www.buymeacoffee.com/apelloni)

Allows to perform simple algebraic operations over a finite field

## Arguments

* `value` - number be represented as `value % modulo`
* `modulo` - An integer corresponding to the size of the modular space.
 For this to be a finite field it must be a **prime number**!

## Operations
* addition
* subtraction
* multiplication
* division
* inversion

## Examples

```rust
// Simple operations within a finite field

use finitefields::{FF,Finitefield,primes};

fn main(){
    // Pick a prime
    let modulo = primes::PRIMES31[0];
    // Define numbers to be cast into our field
    let num1: FF = 23742687;
    let num2: FF = 87129774;

    let fnum1 = Finitefield::new(num1, modulo).unwrap();
    let fnum2 = Finitefield::new(num2, modulo).unwrap();

    // Compute product
    let product = fnum1 * fnum2;
    assert_eq!(product.value, 174523906);

    // Compute the inverse of the product
    let product_inv = product.inverse().unwrap();
    assert_eq!(product_inv.value, 486606559);

    // Multiply by the product
    assert_eq!((product * product_inv).value, 1);
}
```

