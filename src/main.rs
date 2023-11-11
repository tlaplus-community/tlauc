use anyhow::{anyhow, Context, Result};
use clap::{Parser, Subcommand};
use std::fs::File;
use std::io::{Read, Write};
use std::path::Path;
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

    #[arg(
        short,
        long,
        help = "Path to file to use as output; will fail if file already exists unless using --overwrite"
    )]
    output: String,

    #[arg(
        short,
        long,
        default_value_t = false,
        help = "Whether to force a best-effort conversion, ignoring TLA⁺ parse errors"
    )]
    force: bool,

    #[arg(
        long,
        default_value_t = false,
        help = "Whether to overwrite any file existing at the output path; also set by --force"
    )]
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

    if Path::new(&config.output).exists() && !(config.overwrite || config.force) {
        return Err(anyhow!("File already exists at output file location [{}]; use --overwrite flag to overwrite it", &config.output));
    }

    let mut output_file = File::create(&config.output)?;
    match rewrite(&input, &mode, config.force) {
        Ok(output) => {
            output_file.write_all(output.as_bytes()).context(format!("Failed to write to output file [{}]", &config.output))?;
            Ok(())
        },
        Err(TlaError::InputFileParseError { error_lines, .. }) => {
            let line_msg = match error_lines.as_slice() {
                [] => "Could not identify line of first syntax error.".to_string(),
                [..] => format!("Syntax errors might occur on or near the following lines: {:?}.", error_lines)
            };
            Err(anyhow!("Failed to correctly parse input TLA⁺ file; use --force flag to bypass this check.\n".to_string() + &line_msg))
        }
        Err(TlaError::OutputFileParseError{..}) => Err(anyhow!("Failed to correctly parse converted TLA⁺ output; this is a bug, please report it to the maintainer! Use --force to bypass this check (not recommended).")),
        Err(TlaError::InvalidTranslationError { input_tree: _, output_tree: _, output: _, first_diff }) => {
            let err_msg = "Converted TLA⁺ parse tree differs from original; this is a bug, please report it to the maintainer! Use --force to bypass this check (not recommended).";
            Err(anyhow!("{}\n{}", err_msg, first_diff))
        }
    }
}
