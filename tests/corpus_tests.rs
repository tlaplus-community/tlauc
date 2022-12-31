mod corpus_tests {
    use glob::glob;
    use std::ffi::OsStr;
    use std::fs::File;
    use std::io::Read;
    use std::time::Instant;
    use tlauc::{rewrite, Mode, TlaError};

    #[test]
    fn roundtrip_all_example_specs() {
        let start = Instant::now();
        let skip: Vec<&str> = vec![
            // Remove once this PR goes through: https://github.com/tlaplus/Examples/pull/55
            "Reals.tla",
            "Naturals.tla",
            "SimpleRegular.tla",
            // Remove once infix operator edge case is fixed
            "Bakery.tla",
            "Boulanger.tla",
            "LevelSpec.tla",
            "Paxos.tla",
            "Synod.tla",
            "WellFoundedInduction.tla",
        ];
        let skip: Vec<&OsStr> = skip.iter().map(|s| OsStr::new(s)).collect();
        for entry in glob("tests/corpus/**/*.tla").unwrap() {
            if let Ok(path) = entry {
                if skip.contains(&path.file_name().unwrap()) {
                    println!("SKIPPING {:?}", path);
                    continue;
                }

                println!("{:?}", path);
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
                        panic!("Failed to parse input file [{:?}]", path)
                    }
                    Err(TlaError::OutputFileParseError(_)) => {
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
        }

        println!("Corpus tests took {} seconds", start.elapsed().as_secs());
    }
}
