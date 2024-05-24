use std::env;
use std::path::Path;
use std::process::Command;
use std::fs;
use std::time::SystemTime;


fn cargo_add_leanc_Libpath() {
    // Run the command 'leanc --print-ldflags'
    let output = Command::new("leanc")
        .arg("--print-ldflags")
        .output()
        .expect("Failed to execute leanc command");

    // Check if the command was successful
    if output.status.success() {
        // Convert the output to a string
        let output_str = String::from_utf8(output.stdout).expect("Invalid UTF-8 in output");

        // Split the output by '-L' and get the part after '-L'
        let parts: Vec<&str> = output_str.split("-L").collect();
        if parts.len() < 2 {
            eprintln!("Error: No ldflags found after -L");
            return;
        }
        let ldflags = parts[1].split_whitespace().next().unwrap_or_default();

        // Pass ldflags to Cargo as arguments
        println!("cargo:rustc-link-search=native={}", ldflags);
    } else {
        // Print an error message if the command failed
        eprintln!("Error: leanc command failed with status {:?}", output.status);
    }
}

fn cago_add_leanc_libnames() {
    // Add additional library search path
    println!("cargo:rustc-link-search=native=/Users/bollu/.elan/toolchains/leanprover--lean4---nightly/lib/lean");

    // Link against the specified libraries
    println!("cargo:rustc-link-lib=static=leancpp");
    println!("cargo:rustc-link-lib=static=Init");
    println!("cargo:rustc-link-lib=static=Lean");
    println!("cargo:rustc-link-lib=static=leanrt");
    println!("cargo:rustc-link-lib=static=c++");
    println!("cargo:rustc-link-lib=static=Lake");
    
}
// Example custom build script.
fn main() {
    
    // Use the `cc` crate to build a C file and statically link it.
    println!("cargo::rerun-if-changed=libmonodrone/");

    cargo_add_leanc_Libpath();
    cago_add_leanc_libnames();

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

