use std::env;
use std::path::Path;
use std::path::PathBuf;

fn main() {
    println!("cargo:rerun-if-changed=resources/tla-unicode.csv");
    let input_path = Path::new("resources/tla-unicode.csv");
    let output_path = Path::new(&get_output_path()).join("tla-unicode.csv");
    if let Err(e) = std::fs::copy(input_path, output_path) {
        println!("cargo:warning={:?}", e);
        std::process::exit(-1);
    }
}

fn get_output_path() -> PathBuf {
    //<root or manifest path>/target/<profile>/
    let manifest_dir_string = env::var("CARGO_MANIFEST_DIR").unwrap();
    let build_type = env::var("PROFILE").unwrap();
    let path = Path::new(&manifest_dir_string)
        .join("target")
        .join(build_type);
    path
}
