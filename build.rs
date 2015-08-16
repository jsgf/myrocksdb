fn main() {
    println!("cargo:rustc-link-lib=static=rocksdb");
    println!("cargo:rustc-link-search=native=/usr/local/lib");
    println!("cargo:root=/path/to/foo");
    println!("cargo:libdir=/usr/local/lib");
    println!("cargo:include=/usr/local/include");
}
