use anyhow::{anyhow, Context, Result};
use clap::{Parser, Subcommand};
use std::fs::File;
use std::io::{Read, Write};
use tlauc::{rewrite, Mode, TlaError};

#[derive(Debug, Parser)]
#[command(
    author = "Andrew Helwer (ahelwer.ca)",
    version = "0.1.0",
    about = "Converts symbols in TLA⁺ specs to and from unicode",
    long_about = None
)]
struct Args {
    #[command(subcommand)]
    action: Action,
}

#[derive(Debug, Subcommand)]
enum Action {
    Unicode(Config),
    Ascii(Config),
}

#[derive(Debug, Parser)]
struct Config {
    #[arg(short, long)]
    input: String,

    #[arg(short, long)]
    output: String,

    #[arg(short, long)]
    force: bool,

    #[arg(long)]
    overwrite: bool,
}

fn main() -> Result<()> {
    let args = Args::parse();
    match args.action {
        Action::Unicode(config) => convert(&config, Mode::AsciiToUnicode),
        Action::Ascii(config) => convert(&config, Mode::UnicodeToAscii),
    }
}

fn convert(config: &Config, mode: Mode) -> Result<()> {
    let mut input = String::new();
    {
        let mut input_file = File::open(&config.input)
            .context(format!("Failed to open input file [{}]", &config.input))?;
        input_file
            .read_to_string(&mut input)
            .context(format!("Failed to read input file [{}]", &config.input))?;
    }
    match File::options().write(true).create_new(!config.overwrite).open(&config.output) {
        Ok(mut output_file) => {
            match rewrite(&input, mode, config.force) {
                Ok(output) => {
                    output_file.write_all(output.as_bytes()).context(format!("Failed to write to output file [{}]", &config.output))?;
                    Ok(())
                },
                Err(TlaError::InputFileParseError(_)) => Err(anyhow!("Failed to correctly parse input TLA⁺ file; use --force flag to bypass this check.")),
                Err(TlaError::OutputFileParseError(_)) => Err(anyhow!("Failed to correctly parse converted TLA⁺ output; this is a bug, please report it to the maintainer! Use --force to bypass this check (not recommended).")),
                Err(TlaError::InvalidTranslationError { .. }) => Err(anyhow!("Converted TLA⁺ parse tree differs from original; this is a bug, please report it to the maintainer! Use --force to bypass this check (not recommended)."))
            }
        },
        Err(e) => {
            if std::io::ErrorKind::AlreadyExists == e.kind() {
                Err(e).context(format!("File already exists at output file location [{}]; use --overwrite flag to overwrite it", &config.output))?
            } else {
                Err(e).context(format!("Failed to open output file [{}]", &config.output))?
            }
        }
    }
}
