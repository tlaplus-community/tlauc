extern crate clap;
//use clap::{Arg, App, SubCommand};
use tree_sitter::{
    Parser,
    Query,
    QueryCursor,
    Tree,
};
//use std::{fs::File, fs::OpenOptions};
/*
use std::io::{
    prelude::*,
    BufReader,
    BufWriter,
    SeekFrom::Start
};
use std::convert::TryInto;
*/
use std::io::{Error, ErrorKind};
use serde::Deserialize;

#[derive(Debug, Deserialize)]
struct SymbolMapping {
    #[serde(rename = "Name")]
    name : String,
    #[serde(rename = "ASCII")]
    ascii : String,
    #[serde(rename = "Unicode")]
    unicode : String
}

impl SymbolMapping {
    fn canonical_ascii(&self) -> String {
        self.ascii.split(";").next().unwrap().to_string()
    }

    fn ascii_query_str(&self) -> String {
        let query = self.ascii
            .split(";")
            .map(|a| a.replace("\\", "\\\\"))
            .map(|a| format!("\"{}\"", a))
            .reduce(|a, b| a + " " + &b)
            .unwrap();
        let name = &self.name;
        format!("({name} [{query}] @{name})")
    }

    fn unicode_query_str(&self) -> String {
        let name = &self.name;
        let unicode = &self.unicode;
        format!("({name} \"{unicode}\" @{name})")
    }
}

fn get_unicode_mappings() -> Result<Vec<SymbolMapping>, Error> {
    let exe_path = std::env::current_exe()?;
    let exe_dir = exe_path.as_path().parent().ok_or(
        Error::new(ErrorKind::Other, "Exe does not have parent directory")
    )?;
    let csv_path = exe_dir.join("tla-unicode.csv");
    let mut reader = csv::Reader::from_path(csv_path)?;
    let mut records = Vec::new();
    for result in reader.deserialize() {
        let record : SymbolMapping = result?;
        records.push(record);
    }
    
    Ok(records)
}

#[derive(Debug)]
struct JList {
    column: usize,
    bulleted_lines: Vec<usize>
}

#[derive(Debug)]
struct Symbol {
    start: usize,
    end: usize,
    target: String
}

#[derive(Debug)]
struct TlaLine {
    jlists: Vec<JList>,
    symbols: Vec<Symbol>,
    text: String
}

impl TlaLine {
    fn new(line: &str) -> Self {
        TlaLine { jlists: Vec::new(), symbols: Vec::new(), text: line.to_string() }
    }
}

fn rewrite() {
    let input =
r#"---- MODULE Test ----
op == \A n \in Nat : TRUE
op2 == ∀ n \in Nat : TRUE
op3 == \forall n \in Nat : TRUE
===="#.to_string();
    println!("{}", input);
    let mut parser = Parser::new();
    parser.set_language(tree_sitter_tlaplus::language()).expect("Error loading TLA+ grammar");
    let tree = parser.parse(&input, None).unwrap();
    let result = rewrite_generic(&input, &tree, |s| s.ascii_query_str(), |s| s.unicode.to_owned());
    println!("{}", &result);
    let tree = parser.parse(&result, None).unwrap();
    let result = rewrite_generic(&result, &tree, |s| s.unicode_query_str(), |s| s.canonical_ascii().to_owned());
    println!("{}", &result);
}

fn rewrite_generic(
    input: &str,
    tree: &Tree,
    get_query_str: fn(&SymbolMapping) -> String,
    get_target: fn(&SymbolMapping) -> String
) -> String {
    let mappings = get_unicode_mappings().expect("Error loading unicode mappings");

    let queries = &mappings
        .iter()
        .map(|s| get_query_str(s))
        .fold("".to_string(), |a, e| a + &e);
    //println!("{}", queries);
    let query = Query::new(tree_sitter_tlaplus::language(), &queries).unwrap();
    let mut cursor = QueryCursor::new();

    let mut tla_lines : Vec<TlaLine> = input.lines().map(|line| TlaLine::new(line)).collect();
    for capture in cursor.matches(&query, tree.root_node(), "".as_bytes()) {
        let capture = capture.captures[0];
        let mapping = &mappings[capture.index as usize];
        let start_position = capture.node.start_position();
        let end_position = capture.node.end_position();
        assert!(start_position.row == end_position.row);
        let line = &mut tla_lines[start_position.row];
        line.symbols.push(Symbol {
            start: start_position.column,
            end: end_position.column,
            target: get_target(mapping)
        });
    }

    //println!("{:#?}", tla_lines);
    for line in &mut tla_lines {
        for symbol in line.symbols.iter().rev() {
            line.text.replace_range(symbol.start..symbol.end, &symbol.target);
        }
    }

    let result: Vec<&str> = tla_lines.iter().map(|l| l.text.as_ref()).collect();
    result.join("\n")
}

/*
fn rewrite_simple() {
    let mappings = get_unicode_mappings().expect("Error loading unicode mappings");
    let mut input =
r#"---- MODULE Test ----
op == \A n \in Nat : TRUE
op2 == ∀ n \in Nat : TRUE
op3 == \forall n \in Nat : TRUE
===="#.to_string();
    println!("{}", input);
    let mut parser = Parser::new();
    parser.set_language(tree_sitter_tlaplus::language()).expect("Error loading TLA+ grammar");
    let mut tree = parser.parse(&input, None).unwrap();
    let mut cursor = QueryCursor::new();
    while let Some(edit) = rewrite_next_to_unicode(&mappings, &mut input, &tree, &mut cursor) {
        tree.edit(&edit);
        tree = parser.parse(&input, Some(&tree)).unwrap();
    }

    println!("{}", input);

    while let Some(edit) = rewrite_next_to_ascii(&mappings, &mut input, &tree, &mut cursor) {
        tree.edit(&edit);
        tree = parser.parse(&input, Some(&tree)).unwrap();
    }

    println!("{}", input);
}
    */

/*
fn symbol_to_unicode(node_name : &str) -> Option<&str> {
    match node_name {
        "\\A" => Some("∀"),
        "\\in" => Some("∈"),
        "==" => Some("≜"),
        _ => None
    }
}

fn walk_tree(mut cursor : TreeCursor) -> Option<(Node, &str, &str)> {
    loop {
        if let Some(uc) = symbol_to_unicode(cursor.node().kind()) {
            return Some((cursor.node(), cursor.node().kind(), uc));
        }

        // Try to go to first child.
        // If no such child exists, try to go to next sibling.
        // If no such sibling exists, try to go to next sibling of parent.
        // If no such node exists, walk up tree until finding a sibling of a parent.
        // If no parent exists, we have walked the entire tree.
        if !cursor.goto_first_child() {
            loop {
                if cursor.goto_next_sibling() {
                    break;
                } else {
                    if !cursor.goto_parent() {
                        return None;
                    }
                }
            }
        }
    }
}

fn to_unicode(
    spec : &str,
    ignore_errors : bool
) {
    let mut parser = Parser::new();
    parser.set_language(tree_sitter_tlaplus::language()).expect("Error loading TLA+ grammar");

    match OpenOptions::new().read(true).open(spec) {
        Ok(f) => {
            let lines : Vec<String> = BufReader::new(f)
                .lines()
                .map(|l| l.expect("Could not parse line"))
                .collect();
            let tree = parser.parse_with(&mut |_byte: usize, position: Point| -> &[u8] {
                let row = position.row as usize;
                let column = position.column as usize;
                if row < lines.len() {
                    if column < lines[row].as_bytes().len() {
                        &lines[row].as_bytes()[column..]
                    } else {
                        "\n".as_bytes()
                    }
                } else {
                    &[]
                }
            }, None).unwrap();

            if tree.root_node().has_error() && !ignore_errors {
                println!("Cannot translate file due to parse errors; use --ignore-error flag to force translation.");
                std::process::exit(-1);
            }

            if let Some((n, k, uc)) = walk_tree(tree.walk()) {
                match OpenOptions::new().write(true).open(spec) {
                    Ok(f) => {
                        let mut out = BufWriter::new(f);
                        out.seek(Start(n.start_byte().try_into().unwrap()));
                        out.write(uc.as_bytes());
                    }
                    Err(e) => {
                        println!("Error opening file [{}]: [{}]", spec, e);
                        std::process::exit(-1);
                    }
                }
            }

            println!("{}", tree.root_node().has_error());
            println!("{}", tree.root_node().to_sexp());
        }
        Err(e) => {
            println!("Error opening file [{}]: [{}]", spec, e);
            std::process::exit(-1);
        }
    }
}

fn to_ascii(spec : &mut File, ignore_errors : bool) {

}

*/
fn main() {
    rewrite();
    /*
    let matches =
        App::new("TLA+ Unicode Converter")
            .version("0.1.0")
            .author("Andrew Helwer <ahelwer@protonmail.com>")
            .about("Converts symbols in TLA+ specs to and from unicode")
            .arg(Arg::with_name("out_file")
                .short("o")
                .long("out")
                .help("Output file; rewrites input file if not given")
                .takes_value(true)
                .required(false)
            )
            .arg(Arg::with_name("ignore_parse_errors")
                .short("e")
                .long("ignore-error")
                .help("Whether to convert file despite parse errors")
                .required(false)
            )
            .subcommand(SubCommand::with_name("unicode")
                .about("Converts symbols in TLA+ spec to unicode from ASCII")
                .arg(Arg::with_name("spec")
                    .help("The TLA+ spec file to convert")
                    .required(true)
                    .index(1)
                )
            ).subcommand(SubCommand::with_name("ascii")
                .about("Converts symbols in TLA+ spec from unicode to ASCII")
                .arg(Arg::with_name("spec")
                    .help("The TLA+ spec file to convert")
                    .required(true)
                    .index(1)
                )
            ).get_matches();

    let ignore_errors = matches.is_present("ignore_parse_errors");

    if let Some(subcommand_matches) = matches.subcommand_matches("unicode") {
        let mut spec = subcommand_matches.value_of("spec").unwrap();
        if let Some(out_file) = matches.value_of("out_file") {
            if let Err(e) = std::fs::copy(spec, out_file) {
                println!("Failed to copy [{}] to [{}]: {}", spec, out_file, e);
                std::process::exit(-1);
            }

            spec = out_file;
        }

        to_unicode(spec, ignore_errors);
    } else if let Some(matches) = matches.subcommand_matches("ascii") {
        let file_path_str = matches.value_of("spec").unwrap();
        match OpenOptions::new().read(true).write(true).open(file_path_str) {
            Ok(mut spec) => to_ascii(&mut spec, ignore_errors),
            Err(e) => println!("Error opening input file [{}]: [{}]", file_path_str, e)
        }
    } else {
        println!("{}", matches.usage());
    }
    */
}

