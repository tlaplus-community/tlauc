use anyhow::{anyhow, Context, Result};
use clap::{Parser, Subcommand};
use std::fs::File;
use std::io::{Read, Write};
use tlauc::{rewrite, Mode, TlaError};

#[derive(Parser)]
#[command(author, version, about, long_about = None)]
struct Args {
    #[command(subcommand)]
    action: Action,
}

#[derive(Subcommand)]
enum Action {
    #[command(about = "Convert symbols in a TLA⁺ file from ASCII to Unicode")]
    Unicode(Config),

    #[command(about = "Convert symbols in a TLA⁺ file from Unicode to ASCII")]
    Ascii(Config),
}

#[derive(Parser)]
struct Config {
    #[arg(short, long, help = "Path to TLA⁺ file to read as input")]
    input: String,

    #[arg(short, long, help = "Path to file to use as output; will fail if file already exists unless using --overwrite")]
    output: String,

    #[arg(short, long, default_value_t = false, help = "Whether to force a best-effort conversion, ignoring TLA⁺ parse errors")]
    force: bool,

    #[arg(long, default_value_t = false, help = "Whether to overwrite any file existing at the output path; also set by --force")]
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
    match File::options().write(true).create_new(!(config.overwrite || config.force)).open(&config.output) {
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
