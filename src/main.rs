extern crate clap;
//use clap::{Arg, App, SubCommand};
use tree_sitter::{
    Parser,
    Query,
    QueryCursor,
    Tree,
    TreeCursor,
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

enum Mode {
    ASCIItoUnicode,
    UnicodeToASCII
}

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
    fn target_symbol(&self, mode: &Mode) -> String {
        match mode {
            Mode::ASCIItoUnicode => self.unicode.to_string(),
            Mode::UnicodeToASCII => self.ascii.split(";").next().unwrap().to_string()
        }
    }

    fn source_query(&self, mode: &Mode) -> String {
        match mode {
            Mode::ASCIItoUnicode => {
                let query = self.ascii
                    .split(";")
                    .map(|a| a.replace("\\", "\\\\"))
                    .map(|a| format!("\"{}\"", a))
                    .reduce(|a, b| a + " " + &b)
                    .unwrap();
                let name = &self.name;
                format!("({name} [{query}] @{name})")
            },
            Mode::UnicodeToASCII => {
                let name = &self.name;
                let unicode = &self.unicode;
                format!("({name} \"{unicode}\" @{name})")
            }
        }
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

impl JList {
    fn query() -> Query {
        Query::new(
            tree_sitter_tlaplus::language(),
            "(conj_list) @conj_list (disj_list) @disj_list").unwrap()
    }
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

fn mark_jlists(
    tree: &Tree,
    query_cursor: &mut QueryCursor,
    tla_lines: &mut Vec<TlaLine>
) {
    let mut tree_cursor: TreeCursor = tree.walk();
    for capture in query_cursor.matches(&JList::query(), tree.root_node(), "".as_bytes()) {
        let node = capture.captures[0].node;
        let start_line = node.start_position().row;
        tree_cursor.reset(node);
        let mut jlist = JList { column: node.start_position().column, bulleted_lines: Vec::new() };
        tree_cursor.goto_first_child();
        while {
            if "conj_item" == tree_cursor.node().kind() || "disj_item" == tree_cursor.node().kind() {
                jlist.bulleted_lines.push(tree_cursor.node().start_position().row - start_line);
            }

            tree_cursor.goto_next_sibling()
        } {}

        tla_lines[start_line].jlists.push(jlist);
    }
}

fn mark_symbols(
    tree: &Tree,
    cursor: &mut QueryCursor,
    tla_lines: &mut Vec<TlaLine>,
    mode: &Mode
) {
    let mappings = get_unicode_mappings().expect("Error loading unicode mappings");
    let queries = &mappings
        .iter()
        .map(|s| s.source_query(mode))
        .collect::<Vec<String>>()
        .join("");
    let query = Query::new(tree_sitter_tlaplus::language(), &queries).unwrap();

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
            target: mapping.target_symbol(mode)
        });
    }
}

fn replace_symbols(tla_lines: &mut Vec<TlaLine>) {
    for line in tla_lines {
        for symbol in line.symbols.iter().rev() {
            line.text.replace_range(symbol.start..symbol.end, &symbol.target);
        }
    }
}

fn rewrite_generic(
    input: &str,
    tree: &Tree,
    mode: Mode
) -> String {
    let mut cursor = QueryCursor::new();
    let mut tla_lines : Vec<TlaLine> = input.lines().map(|line| TlaLine::new(line)).collect();

    mark_jlists(tree, &mut cursor, &mut tla_lines);
    mark_symbols(tree, &mut cursor, &mut tla_lines, &mode);
    println!("{:#?}", tla_lines);
    replace_symbols(&mut tla_lines);

    tla_lines.iter().map(|l| l.text.as_ref()).collect::<Vec<&str>>().join("\n")
}

fn rewrite() {
    let input =
r#"---- MODULE Test ----
op == \A n \in Nat : TRUE
op2 == /\ A
       /\ \/ B /\ C
          \/ D
       /\ E
===="#.to_string();
    println!("{}", input);
    let mut parser = Parser::new();
    parser.set_language(tree_sitter_tlaplus::language()).expect("Error loading TLA+ grammar");
    let tree = parser.parse(&input, None).unwrap();
    let result = rewrite_generic(&input, &tree, Mode::ASCIItoUnicode);
    println!("{}", &result);
    let tree = parser.parse(&result, None).unwrap();
    let result = rewrite_generic(&result, &tree, Mode::UnicodeToASCII);
    println!("{}", &result);
}

/*
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

