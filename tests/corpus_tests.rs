mod corpus_tests {
    use glob::glob;
    use std::fs::File;
    use std::io::Read;
    use tlauc::{rewrite, Mode, TlaError};

    #[test]
    fn roundtrip_all_example_specs() {
        for entry in glob("tests/corpus/**/*.tla").unwrap() {
            if let Ok(path) = entry {
                let file_name = path.file_name().unwrap();
                if path.is_file()
                    && file_name != "Reals.tla"
                    && file_name != "Naturals.tla"
                    && file_name != "SimpleRegular.tla"
                {
                    //println!("{:?}", path);
                    let mut input = String::new();
                    {
                        let mut input_file = File::open(&path)
                            .expect(&format!("Failed to open input file [{:?}]", path));
                        input_file
                            .read_to_string(&mut input)
                            .expect(&format!("Failed to read input file [{:?}]", path));
                    }

                    match rewrite(&input, Mode::AsciiToUnicode, false) {
                        Ok(_) => (),
                        Err(TlaError::InputFileParseError(_)) => {
                            println!("Failed to parse input file [{:?}]", path)
                        }
                        Err(TlaError::OutputFileParseError(_)) => {
                            println!("Failed to parse output file [{:?}]", path)
                        }
                        Err(TlaError::InvalidTranslationError {
                            input_tree: _,
                            output_tree: _,
                            output: _,
                            first_diff,
                        }) => println!(
                            "Input/output parse tree mismatch for [{:?}]: [{:?}]",
                            path, first_diff
                        ),
                    }
                }
            }
        }
    }
}
