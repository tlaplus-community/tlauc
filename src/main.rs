extern crate clap;
use clap::{Arg, App, SubCommand};
use tree_sitter::{Node, Parser, Point, Tree, TreeCursor, Query, QueryCursor};
use std::{fs::File, fs::OpenOptions};
use std::io::{
    prelude::*,
    BufReader,
    BufWriter,
    SeekFrom::Start
};
use std::convert::TryInto;

fn has_forall(tree : Tree) -> bool {
    match Query::new(tree_sitter_tlaplus::language(), "(forall) @match") {
        Ok(q) => {
            let qc = QueryCursor::new();
            qc.matches(&q, tree.root_node(), |_ : &Node| {});
        },
        Err(e) => {}
    };

    return false;
}

fn symbol_to_unicode(node_name : &str) -> Option<&str> {
    match node_name {
        "\\A" => Some("∀"),
        "\\in" => Some("∈"),
        "==" => Some("≜"),
        _ => None
    }
}

/**
 * Inefficient; we don't need to walk the entire tree! We can use queries!
 */
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

fn main() {
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
}

