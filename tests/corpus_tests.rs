mod corpus_tests {
    use glob::glob;
    use rayon::prelude::*;
    use std::ffi::OsStr;
    use std::fs::File;
    use std::io::Read;
    use std::path::PathBuf;
    use std::time::Instant;
    use tlauc::{rewrite, Mode, TlaError};

    fn unwrap_conversion(input: Result<String, TlaError>, path: &PathBuf) -> String {
        match input {
            Ok(converted) => converted,
            Err(TlaError::InputFileParseError(_)) => {
                panic!("Failed to parse input file [{:?}]", path)
            }
            Err(TlaError::OutputFileParseError { .. }) => {
                panic!("Failed to parse output file [{:?}]", path)
            }
            Err(TlaError::InvalidTranslationError {
                input_tree: _,
                output_tree: _,
                output: _,
                first_diff,
            }) => panic!(
                "Input/output parse tree mismatch for [{:?}]: [{:?}]",
                path, first_diff
            ),
        }
    }

    #[test]
    fn roundtrip_all_example_specs() {
        let start = Instant::now();
        let skip: Vec<&str> = vec![
            "SomeSpecName.tla"
        ];
        println!("SKIPPING {:?}", skip);
        let skip: Vec<&OsStr> = skip.iter().map(|s| OsStr::new(s)).collect();
        let paths: Vec<PathBuf> = glob("tests/corpus/**/*.tla")
            .unwrap()
            .into_iter()
            .filter_map(|path| path.ok())
            .filter(|path| !skip.contains(&path.file_name().unwrap()))
            .collect();

        paths.par_iter().for_each(|path| {
            println!("{:?}", path);
            let mut input = String::new();
            {
                let mut input_file =
                    File::open(&path).expect(&format!("Failed to open input file [{:?}]", path));
                input_file
                    .read_to_string(&mut input)
                    .expect(&format!("Failed to read input file [{:?}]", path));
            }

            let intermediate =
                unwrap_conversion(rewrite(&input, &Mode::AsciiToUnicode, false), path);
            unwrap_conversion(rewrite(&intermediate, &Mode::UnicodeToAscii, false), path);
        });

        println!("Corpus tests took {} seconds", start.elapsed().as_secs());
    }
}
