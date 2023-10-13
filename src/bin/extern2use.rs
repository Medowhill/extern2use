use std::path::PathBuf;

use clap::Parser;
use extern2use::*;

#[derive(Parser, Debug)]
struct Args {
    #[clap(short, long)]
    output: PathBuf,
    input: PathBuf,
}

fn main() {
    let args = Args::parse();

    assert!(resolve::check(&args.input), "initial");
    resolve::rename_unnamed(&args.input);
    assert!(resolve::check(&args.input), "after renaming");
    resolve::deduplicate(&args.input);
    assert!(resolve::check(&args.input), "after deduplication");
}
