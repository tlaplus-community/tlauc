extern crate clap;
//use clap::{Arg, App, SubCommand};
use tree_sitter::{
    InputEdit,
    Node, 
    Parser,
    Point,
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
    fn canonical_ascii(&self) -> &str {
        return self.ascii.split(";").next().unwrap();
    }

    fn ascii_query(&self) -> Query {
        let query = self.ascii
            .split(";")
            .map(|a| a.replace("\\", "\\\\"))
            .map(|a| format!("\"{}\"", a))
            .reduce(|a, b| a + " " + &b)
            .unwrap();
        let query = format!("({} [{}] @match)", self.name, query);
        return Query::new(tree_sitter_tlaplus::language(), &query).unwrap();
    }

    fn to_ascii(&self, text : &mut String, node : &Node) -> InputEdit {
        *text = text[..node.start_byte()].to_string()
            + self.canonical_ascii()
            + &text[node.end_byte()..];
        return InputEdit {
            start_byte: node.start_byte(),
            old_end_byte: node.end_byte(),
            new_end_byte: node.start_byte() + self.canonical_ascii().len(),
            start_position: node.start_position(),
            old_end_position: node.end_position(),
            new_end_position: Point::new(node.start_position().row, node.start_position().column + self.canonical_ascii().len())
        };
    }
    
    fn unicode_query(&self) -> Query {
        let query = format!("({} \"{}\" @match)", self.name, self.unicode);
        return Query::new(tree_sitter_tlaplus::language(), &query).unwrap();
    }
    
    fn to_unicode(&self, text : &mut String, node : &Node) -> InputEdit {
        *text = text[..node.start_byte()].to_string()
            + self.unicode.as_str()
            + &text[node.end_byte()..];
        return InputEdit {
            start_byte: node.start_byte(),
            old_end_byte: node.end_byte(),
            new_end_byte: node.start_byte() + self.unicode.len(),
            start_position: node.start_position(),
            old_end_position: node.end_position(),
            new_end_position: Point::new(node.start_position().row, node.start_position().column + self.unicode.len())
        };
    }
}

fn get_unicode_mappings() -> Result<Vec<SymbolMapping>, Error> {
    let exe_path = std::env::current_exe()?;
    let exe_dir = exe_path.as_path().parent().ok_or(
        Error::new(ErrorKind::Other, "Exe does not have parent")
    )?;
    let csv_path = exe_dir.join("tla-unicode.csv");
    let mut reader = csv::Reader::from_path(csv_path)?;
    let mut records = Vec::new();
    for result in reader.deserialize() {
        let record : SymbolMapping = result?;
        records.push(record);
    }
    
    return Ok(records);
}

fn rewrite_next_to_unicode(
    mappings : &Vec<SymbolMapping>,
    text : &mut String,
    tree : &Tree,
    cursor : &mut QueryCursor
) -> Option<InputEdit> {
    for mapping in mappings {
        //println!("Mapping [{}] -> [{}]", mapping.ascii[0], mapping.unicode);
        let query = mapping.ascii_query();
        for m in cursor.matches(&query, tree.root_node(), "".as_bytes()) {
            for c in m.captures {
                println!("{:?}", c);
                return Some(mapping.to_unicode(text, &c.node));
            }
        }
    }
    
    return None;
}

fn rewrite_next_to_ascii(
    mappings : &Vec<SymbolMapping>,
    text : &mut String,
    tree : &Tree,
    cursor : &mut QueryCursor
) -> Option<InputEdit> {
    for mapping in mappings {
        //println!("Mapping [{}] -> [{}]", mapping.ascii[0], mapping.unicode);
        let query = mapping.unicode_query();
        for m in cursor.matches(&query, tree.root_node(), "".as_bytes()) {
            for c in m.captures {
                println!("{:?}", c);
                return Some(mapping.to_ascii(text, &c.node));
            }
        }
    }
    
    return None;
}


fn rewrite() {
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

