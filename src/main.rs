use anyhow::{anyhow, Context, Result};
use clap::Parser;
use std::fs::File;
use std::io::{Read, Write};
use std::path::{Path, PathBuf};
use tlauc::{rewrite, Mode, TlaError};

#[derive(Parser)]
#[command(author, version, about, long_about = None)]
struct Args {
    #[arg(help = "Path to TLA⁺ file to convert")]
    input: PathBuf,

    #[arg(
        short,
        long,
        help = "Optional path to output; will overwrite input file by default"
    )]
    output: Option<PathBuf>,

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
        help = "Convert the TLA⁺ file to ASCII instead of Unicode"
    )]
    ascii: bool,
}

fn main() -> Result<()> {
    let args = Args::parse();
    let output_path = if let Some(output_path) = args.output {
        output_path
    } else {
        args.input.clone()
    };
    convert(
        args.input.as_path(),
        output_path.as_path(),
        if args.ascii {
            Mode::UnicodeToAscii
        } else {
            Mode::AsciiToUnicode
        },
        args.force,
    )
}

fn convert(input_path: &Path, output_path: &Path, mode: Mode, force: bool) -> Result<()> {
    let mut input = String::new();
    {
        let mut input_file = File::open(input_path)
            .context(format!("Failed to open input file [{:?}]", input_path))?;
        input_file
            .read_to_string(&mut input)
            .context(format!("Failed to read input file [{:?}]", input_path))?;
    }

    match rewrite(&input, &mode, force) {
        Ok(output) => {
            let mut output_file = File::create(output_path)?;
            output_file.write_all(output.as_bytes()).context(format!("Failed to write to output file [{:?}]", output_path))?;
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    // https://github.com/tlaplus-community/tlauc/issues/14
    fn test_input_file_unchanged_on_parse_failure() {
        let project_root = std::env::var("CARGO_MANIFEST_DIR").unwrap();
        let input_path = PathBuf::from(project_root)
            .join("tests")
            .join("InvalidSyntax.tla");
        let expected = std::fs::read_to_string(&input_path).unwrap();
        let output_path = input_path.clone();
        let result: Result<()> = convert(
            input_path.as_path(),
            output_path.as_path(),
            tlauc::Mode::AsciiToUnicode,
            false,
        );
        assert!(result.is_err());
        let actual = std::fs::read_to_string(&output_path).unwrap();
        assert_eq!(expected, actual);
    }

    #[test]
    fn test_blank_input_file() {
        let project_root = std::env::var("CARGO_MANIFEST_DIR").unwrap();
        let input_path = PathBuf::from(project_root)
            .join("tests")
            .join("BlankFile.tla");
        let output_path = input_path.clone();
        let result: Result<()> = convert(
            input_path.as_path(),
            output_path.as_path(),
            tlauc::Mode::AsciiToUnicode,
            false,
        );
        assert!(result.is_err());
    }
}
