use std::{
    fs,
    path::{Path, PathBuf},
};

use clap::Parser;
use extern2use::*;

#[derive(Parser, Debug)]
struct Args {
    #[clap(short, long)]
    output: Option<PathBuf>,
    input: PathBuf,
}

fn main() {
    let mut args = Args::parse();

    let dir = if let Some(output) = &mut args.output {
        output.push(args.input.file_name().unwrap());
        if output.exists() {
            assert!(output.is_dir());
            clear_dir(&output);
        } else {
            fs::create_dir(&output).unwrap();
        }
        copy_dir(&args.input, &output, true);
        output
    } else {
        &args.input
    };
    let file = dir.join("c2rust-lib.rs");

    println!("rename unnamed");
    while resolve::rename_unnamed(&file) {}

    println!("deduplicate types");
    resolve::deduplicate_types(&file);

    println!("deduplicate type aliases");
    while resolve::deduplicate_type_aliases(&file) {}

    println!("deduplicate functions");
    resolve::deduplicate_fns(&file);

    println!("resolve conflicts");
    resolve::resolve_conflicts(&file);

    println!("add bin");
    resolve::add_bin(&file);
}

fn clear_dir<P: AsRef<Path>>(path: P) {
    for entry in fs::read_dir(path).unwrap() {
        let entry_path = entry.unwrap().path();
        if entry_path.is_dir() {
            fs::remove_dir_all(entry_path).unwrap();
        } else {
            fs::remove_file(entry_path).unwrap();
        }
    }
}

fn copy_dir<P: AsRef<Path>, Q: AsRef<Path>>(src: P, dst: Q, root: bool) {
    for entry in fs::read_dir(src).unwrap() {
        let src_path = entry.unwrap().path();
        let name = src_path.file_name().unwrap();
        let dst_path = dst.as_ref().join(name);
        if src_path.is_file() {
            fs::copy(src_path, dst_path).unwrap();
        } else if src_path.is_dir() && (!root || name != "target") {
            fs::create_dir(&dst_path).unwrap();
            copy_dir(src_path, dst_path, false);
        }
    }
}
