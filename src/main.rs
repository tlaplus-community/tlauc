use anyhow::{anyhow, Context, Result};
use clap::Parser;
use std::collections::HashSet;
use std::fs::File;
use std::io::{Read, Write};
use std::path::{Path, PathBuf};
use tlauc::{rewrite, Mode, SymbolMapping, TlaError};

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

    #[arg(
        long,
        help = "Symbol to skip translating. All symbol aliases are also skipped. Can define multiple. Two formats are recognized:
 1. A literal alias of the symbol to skip, like \"\\leq\" or \"∀\".
 2. Supported keywords as shorthand for groups of symbols:
   - \"numsets\" refers to ℕ, ℤ, and ℝ
   - \"contractions\" refers to ∷, ‥, …, ≔, ⩴, ‖, ‼, and ⁇"
    )]
    skip: Vec<String>,
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
        args.skip,
    )
}

fn convert(
    input_path: &Path,
    output_path: &Path,
    mode: Mode,
    force: bool,
    skip: Vec<String>,
) -> Result<()> {
    let mut input = String::new();
    {
        let mut input_file = File::open(input_path)
            .context(format!("Failed to open input file [{:?}]", input_path))?;
        input_file
            .read_to_string(&mut input)
            .context(format!("Failed to read input file [{:?}]", input_path))?;
    }

    match rewrite(&input, &mode, force, symbol_filter(skip_symbols(skip))) {
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

const NUMSETS: [&'static str; 6] = ["Nat", "ℕ", "Int", "ℤ", "Real", "ℝ"];

const CONTRACTIONS: [&'static str; 8] = ["∷", "‥", "…", "≔", "⩴", "‖", "‼", "⁇"];

fn skip_symbols(skip: Vec<String>) -> HashSet<String> {
    skip.iter()
        .map(|name| match name.as_str() {
            "numsets" => NUMSETS.into_iter().collect(),
            "contractions" => CONTRACTIONS.into_iter().collect(),
            val => vec![val],
        })
        .flatten()
        .map(|s| s.to_owned())
        .collect()
}

fn symbol_filter(skip_symbol: HashSet<String>) -> impl Fn(&SymbolMapping) -> bool {
    move |symbol| {
        !&symbol
            .ascii
            .iter()
            .any(|literal| skip_symbol.contains(literal))
            && !skip_symbol.contains(&symbol.unicode)
    }
}

#[cfg(test)]
mod tests {
    use std::iter::once;
    use tlauc::get_unicode_mappings;

    use super::*;

    #[test]
    fn test_skip_keyword_parsing() {
        assert_eq!(
            skip_symbols(vec!["numsets".to_owned()]),
            NUMSETS.into_iter().map(|val| val.to_owned()).collect()
        );
        assert_eq!(
            skip_symbols(vec!["contractions".to_owned()]),
            CONTRACTIONS.into_iter().map(|val| val.to_owned()).collect()
        );
        assert_eq!(
            skip_symbols(vec!["numsets".to_owned(), "contractions".to_owned()]),
            CONTRACTIONS
                .into_iter()
                .chain(NUMSETS)
                .map(|val| val.to_owned())
                .collect()
        );
        assert_eq!(
            skip_symbols(vec![
                "<=".to_owned(),
                "numsets".to_owned(),
                "\\/".to_owned()
            ]),
            NUMSETS
                .into_iter()
                .chain(once("<="))
                .chain(once("\\/"))
                .map(|val| val.to_owned())
                .collect()
        );
        assert_eq!(
            skip_symbols(vec![
                "contractions".to_owned(),
                "<=".to_owned(),
                "numsets".to_owned(),
                "\\/".to_owned()
            ]),
            CONTRACTIONS
                .into_iter()
                .chain(NUMSETS)
                .chain(once("<="))
                .chain(once("\\/"))
                .map(|val| val.to_owned())
                .collect()
        );
    }

    #[test]
    fn test_skip_filters() {
        let mappings = get_unicode_mappings();
        let filter = symbol_filter(skip_symbols(vec!["numsets".to_owned()]));
        assert!(!filter(
            mappings
                .iter()
                .find(|s| s.name.eq("nat_number_set"))
                .unwrap()
        ));
        assert!(!filter(
            mappings
                .iter()
                .find(|s| s.name.eq("int_number_set"))
                .unwrap()
        ));
        assert!(!filter(
            mappings
                .iter()
                .find(|s| s.name.eq("real_number_set"))
                .unwrap()
        ));
        assert!(filter(
            mappings.iter().find(|s| s.name.eq("label_as")).unwrap()
        ));
        assert!(filter(
            mappings.iter().find(|s| s.name.eq("dots_2")).unwrap()
        ));
        assert!(filter(
            mappings.iter().find(|s| s.name.eq("dots_3")).unwrap()
        ));
        assert!(filter(
            mappings.iter().find(|s| s.name.eq("assign")).unwrap()
        ));
        assert!(filter(
            mappings.iter().find(|s| s.name.eq("bnf_rule")).unwrap()
        ));
        assert!(filter(
            mappings.iter().find(|s| s.name.eq("vertvert")).unwrap()
        ));
        assert!(filter(mappings.iter().find(|s| s.name.eq("excl")).unwrap()));
        assert!(filter(mappings.iter().find(|s| s.name.eq("qq")).unwrap()));
        let filter = symbol_filter(skip_symbols(vec!["contractions".to_owned()]));
        assert!(filter(
            mappings
                .iter()
                .find(|s| s.name.eq("nat_number_set"))
                .unwrap()
        ));
        assert!(filter(
            mappings
                .iter()
                .find(|s| s.name.eq("int_number_set"))
                .unwrap()
        ));
        assert!(filter(
            mappings
                .iter()
                .find(|s| s.name.eq("real_number_set"))
                .unwrap()
        ));
        assert!(!filter(
            mappings.iter().find(|s| s.name.eq("label_as")).unwrap()
        ));
        assert!(!filter(
            mappings.iter().find(|s| s.name.eq("dots_2")).unwrap()
        ));
        assert!(!filter(
            mappings.iter().find(|s| s.name.eq("dots_3")).unwrap()
        ));
        assert!(!filter(
            mappings.iter().find(|s| s.name.eq("assign")).unwrap()
        ));
        assert!(!filter(
            mappings.iter().find(|s| s.name.eq("bnf_rule")).unwrap()
        ));
        assert!(!filter(
            mappings.iter().find(|s| s.name.eq("vertvert")).unwrap()
        ));
        assert!(!filter(
            mappings.iter().find(|s| s.name.eq("excl")).unwrap()
        ));
        assert!(!filter(mappings.iter().find(|s| s.name.eq("qq")).unwrap()));
        let filter = symbol_filter(skip_symbols(vec![
            "numsets".to_owned(),
            "contractions".to_owned(),
        ]));
        assert!(!filter(
            mappings
                .iter()
                .find(|s| s.name.eq("nat_number_set"))
                .unwrap()
        ));
        assert!(!filter(
            mappings
                .iter()
                .find(|s| s.name.eq("int_number_set"))
                .unwrap()
        ));
        assert!(!filter(
            mappings
                .iter()
                .find(|s| s.name.eq("real_number_set"))
                .unwrap()
        ));
        assert!(!filter(
            mappings.iter().find(|s| s.name.eq("label_as")).unwrap()
        ));
        assert!(!filter(
            mappings.iter().find(|s| s.name.eq("dots_2")).unwrap()
        ));
        assert!(!filter(
            mappings.iter().find(|s| s.name.eq("dots_3")).unwrap()
        ));
        assert!(!filter(
            mappings.iter().find(|s| s.name.eq("assign")).unwrap()
        ));
        assert!(!filter(
            mappings.iter().find(|s| s.name.eq("bnf_rule")).unwrap()
        ));
        assert!(!filter(
            mappings.iter().find(|s| s.name.eq("vertvert")).unwrap()
        ));
        assert!(!filter(
            mappings.iter().find(|s| s.name.eq("excl")).unwrap()
        ));
        assert!(!filter(mappings.iter().find(|s| s.name.eq("qq")).unwrap()));
        let filter = symbol_filter(skip_symbols(vec![
            "<=".to_owned(),
            "/\\".to_owned(),
            "\\/".to_owned(),
        ]));
        assert!(!filter(mappings.iter().find(|s| s.name.eq("leq")).unwrap()));
        assert!(!filter(
            mappings.iter().find(|s| s.name.eq("land")).unwrap()
        ));
        assert!(!filter(mappings.iter().find(|s| s.name.eq("lor")).unwrap()));
        assert!(filter(
            mappings
                .iter()
                .find(|s| s.name.eq("nat_number_set"))
                .unwrap()
        ));
        assert!(filter(
            mappings
                .iter()
                .find(|s| s.name.eq("int_number_set"))
                .unwrap()
        ));
        assert!(filter(
            mappings
                .iter()
                .find(|s| s.name.eq("real_number_set"))
                .unwrap()
        ));
        assert!(filter(
            mappings.iter().find(|s| s.name.eq("label_as")).unwrap()
        ));
        assert!(filter(
            mappings.iter().find(|s| s.name.eq("dots_2")).unwrap()
        ));
        assert!(filter(
            mappings.iter().find(|s| s.name.eq("dots_3")).unwrap()
        ));
        assert!(filter(
            mappings.iter().find(|s| s.name.eq("assign")).unwrap()
        ));
        assert!(filter(
            mappings.iter().find(|s| s.name.eq("bnf_rule")).unwrap()
        ));
        assert!(filter(
            mappings.iter().find(|s| s.name.eq("vertvert")).unwrap()
        ));
        assert!(filter(mappings.iter().find(|s| s.name.eq("excl")).unwrap()));
        assert!(filter(mappings.iter().find(|s| s.name.eq("qq")).unwrap()));
    }

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
            vec![],
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
            vec![],
        );
        assert!(result.is_err());
    }
}
