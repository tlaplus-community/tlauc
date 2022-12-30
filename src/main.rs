//use tlauc::{rewrite, Mode};
use clap::{Parser, Subcommand};

#[derive(Debug, Parser)]
#[command(
    author = "Andrew Helwer (ahelwer.ca)",
    version = "0.1.0",
    about = "Converts symbols in TLA+ specs to and from unicode",
    long_about = None
)]
struct Args {
    #[command(subcommand)]
    action: Action,

    #[arg(short, long)]
    input: String,

    #[arg(short, long)]
    output: String,

    #[arg(short, long)]
    force: bool,
}

#[derive(Debug, Subcommand)]
enum Action {
    Ascii,
    Unicode,
}

fn main() {
    let args = Args::parse();
    println!("{:#?}", args);
}
