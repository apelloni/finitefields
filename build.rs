extern crate cc;

fn main() {
    //println!("cargo:rustc-link-lib=stdc++");
    //println!("cargo:rustc-link-lib=gcc");

    cc::Build::new().file("src/mul_mod.c")
        .opt_level(3)
        .flag("-Wall")
        .flag("-ffast-math")
        .compile("libmulmod.a");
}
