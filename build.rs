use std::env;
use std::path::Path;
use std::process::Command;
use std::fs;
use std::time::SystemTime;

// Example custom build script.
fn main() {
    // Use the `cc` crate to build a C file and statically link it.
    println!("cargo::rerun-if-changed=libmonodrone/");
    let monodrone_dir = "./";
    let lib_path = format!("{}/.lake/build/lib/libMonodrone.a", monodrone_dir);
    let status = Command::new("lake")
        .arg("build")
        .current_dir(monodrone_dir)
        .status()
         .expect("Failed to execute lake build");
    // Link against the library
    println!("cargo:rustc-link-search=native={}/.lake/build/lib", monodrone_dir);
    println!("cargo:rustc-link-lib=static=Monodrone");
    
}

