use std::env;
use std::path::Path;
use std::process::Command;
use std::fs;
use std::time::SystemTime;


fn cargo_add_ld_options() {
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
        let ld_search_path = parts[1].split_whitespace().next().unwrap_or_default();
        println!("cargo::warning='ld_search_path is {ld_search_path}'");

        // Pass search_path to Cargo as arguments
        println!("cargo:rustc-link-search=native={}", ld_search_path);
        return; 

        let lib_names : Vec<&str> = parts.iter().skip(2).map(|part| {
            part.split_whitespace().next().unwrap_or_default()
        }).collect();

        eprintln!("error: lib names: {:?}", lib_names);
        
    } else {
        // Print an error message if the command failed
        eprintln!("Error: leanc command failed with status {:?}", output.status);
    }
}

// Example custom build script.
fn main() {
    
    // Use the `cc` crate to build a C file and statically link it.
    println!("cargo::rerun-if-changed=lakefile.lean");
    println!("cargo::rerun-if-changed=Monodrone/");
    println!("cargo::rerun-if-changed=Monodrone.lean");

    cargo_add_ld_options();

    let monodrone_dir = "./";
    let status = Command::new("lake")
        .arg("build")
        .arg("Monodrone:fatStatic")
        .current_dir(monodrone_dir)
        .status()
        .expect("Failed to execute lake build");
    // Link against the library
    println!("cargo:rustc-link-search=native={}/.lake/build/lib", monodrone_dir);
    println!("cargo:rustc-link-lib=static=MonodroneFat");
    
}

