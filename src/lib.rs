mod strquantity;
use crate::strquantity::{ByteQuantity, CharQuantity};

use serde::Deserialize;
use std::io::Error;
use std::ops::Range;
use tree_sitter::{Parser, Query, QueryCursor, Tree, TreeCursor};

pub enum Mode {
    AsciiToUnicode,
    UnicodeToAscii,
}

#[derive(Debug)]
pub enum TlaError {
    InputFileParseError(Tree),
    InvalidTranslationError {
        input_tree: Tree,
        output_tree: Tree,
        output: String,
    },
}

pub fn rewrite(input: &str, mode: Mode, force: bool) -> Result<String, TlaError> {
    // Parse input TLA+ file and construct data structures to hold information about it
    let mut parser = Parser::new();
    parser
        .set_language(tree_sitter_tlaplus::language())
        .expect("Error loading TLA+ grammar");
    let input_tree = parser.parse(&input, None).unwrap();
    if !force && input_tree.root_node().has_error() {
        return Err(TlaError::InputFileParseError(input_tree));
    }

    let mut cursor = QueryCursor::new();
    let mut tla_lines = TlaLine::construct_from(input);

    // Identify & replace symbols
    mark_jlists(&input_tree, &mut cursor, &mut tla_lines);
    mark_symbols(&input_tree, &mut cursor, &mut tla_lines, &mode);
    replace_symbols(&mut tla_lines);

    // Ensure output parse tree is identical to input parse tree
    let output = tla_lines
        .iter()
        .map(|l| l.text.as_ref())
        .collect::<Vec<&str>>()
        .join("\n");
    let output_tree = parser.parse(&output, None).unwrap();
    if !force
        && (output_tree.root_node().has_error()
            || input_tree.root_node().to_sexp() != output_tree.root_node().to_sexp())
    {
        return Err(TlaError::InvalidTranslationError {
            input_tree,
            output_tree,
            output,
        });
    }

    Ok(output)
}

pub fn get_unicode_mappings() -> Result<Vec<SymbolMapping>, Error> {
    let csv = include_str!("../resources/tla-unicode.csv");
    let mut reader = csv::Reader::from_reader(csv.as_bytes());
    let mut records = Vec::new();
    for result in reader.deserialize() {
        let record: SymbolMapping = result?;
        records.push(record);
    }

    Ok(records)
}

#[derive(Debug, Deserialize)]
pub struct SymbolMapping {
    #[serde(rename = "Name")]
    name: String,
    #[serde(rename = "ASCII")]
    ascii: String,
    #[serde(rename = "Unicode")]
    unicode: String,
}

impl SymbolMapping {
    pub fn canonical_ascii(&self) -> &str {
        self.ascii.split(";").next().unwrap()
    }

    pub fn ascii_query(&self) -> String {
        let query = self
            .ascii
            .split(";")
            .map(|a| a.replace("\\", "\\\\"))
            .map(|a| format!("\"{}\"", a))
            .reduce(|a, b| a + " " + &b)
            .unwrap();
        let name = &self.name;
        format!("({name} [{query}] @{name})")
    }

    pub fn unicode_query(&self) -> String {
        let name = &self.name;
        let unicode = &self.unicode;
        format!("({name} \"{unicode}\" @{name})")
    }

    fn target_symbol(&self, mode: &Mode) -> &str {
        match mode {
            Mode::AsciiToUnicode => &self.unicode,
            Mode::UnicodeToAscii => self.canonical_ascii(),
        }
    }

    fn source_query(&self, mode: &Mode) -> String {
        match mode {
            Mode::AsciiToUnicode => self.ascii_query(),
            Mode::UnicodeToAscii => self.unicode_query(),
        }
    }

    fn chars_added(&self, mode: &Mode, src_symbol: &str) -> CharQuantity<i8> {
        match mode {
            Mode::AsciiToUnicode => CharQuantity(
                (self.unicode.chars().count() as i8) - (src_symbol.chars().count() as i8),
            ),
            Mode::UnicodeToAscii => CharQuantity(
                (self.canonical_ascii().chars().count() as i8)
                    - (self.unicode.chars().count() as i8),
            ),
        }
    }
}

#[derive(Debug)]
struct TlaLine {
    text: String,
    jlists: Vec<JList>,
    symbols: Vec<Symbol>,
}

impl TlaLine {
    fn construct_from(input: &str) -> Vec<Self> {
        input
            .lines()
            .map(|line| TlaLine {
                jlists: Vec::new(),
                symbols: Vec::new(),
                text: line.to_string(),
            })
            .collect()
    }

    fn shift(
        &mut self,
        char_diff: CharQuantity<i8>,
        char_diff_start_index: CharQuantity<usize>,
        byte_diff: ByteQuantity<i8>,
        byte_diff_start_index: ByteQuantity<usize>,
    ) {
        for jlist in &mut self.jlists {
            if jlist.char_column > char_diff_start_index {
                //jlist.char_column = CharQuantity((jlist.char_column as i32 + char_diff as i32) as usize);
                jlist.char_column = jlist.char_column + char_diff;
            }
        }

        for symbol in &mut self.symbols {
            if symbol.src_byte_range.start > byte_diff_start_index {
                symbol.src_byte_range = (symbol.src_byte_range.start + byte_diff)
                    ..(symbol.src_byte_range.end + byte_diff);
            }
        }
    }
}

fn mark_jlists(tree: &Tree, query_cursor: &mut QueryCursor, tla_lines: &mut [TlaLine]) {
    let mut tree_cursor: TreeCursor = tree.walk();
    for capture in query_cursor.matches(&JList::query(), tree.root_node(), "".as_bytes()) {
        let node = capture.captures[0].node;
        let start_line = node.start_position().row;
        let line = &mut tla_lines[start_line];
        let char_column = CharQuantity(line.text[..node.start_position().column].chars().count());
        let mut jlist = JList {
            char_column,
            bullet_line_offsets: Vec::new(),
        };
        tree_cursor.reset(node);
        tree_cursor.goto_first_child();
        while {
            if JList::is_jlist_item_node(&tree_cursor) {
                jlist
                    .bullet_line_offsets
                    .push(tree_cursor.node().start_position().row - start_line);
            }

            tree_cursor.goto_next_sibling()
        } {}

        line.jlists.push(jlist);
    }
}

#[derive(Debug)]
struct JList {
    char_column: CharQuantity<usize>,
    bullet_line_offsets: Vec<usize>,
}

impl JList {
    fn query() -> Query {
        Query::new(
            tree_sitter_tlaplus::language(),
            "(conj_list) @conj_list (disj_list) @disj_list",
        )
        .unwrap()
    }

    fn is_jlist_item_node(cursor: &TreeCursor) -> bool {
        "conj_item" == cursor.node().kind() || "disj_item" == cursor.node().kind()
    }
}

fn mark_symbols(tree: &Tree, cursor: &mut QueryCursor, tla_lines: &mut [TlaLine], mode: &Mode) {
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
        let src_byte_range = ByteQuantity(start_position.column)..ByteQuantity(end_position.column);
        let src_symbol = &line.text[ByteQuantity::as_range(&src_byte_range)];
        let target = mapping.target_symbol(mode).to_string();
        line.symbols.push(Symbol {
            char_diff: mapping.chars_added(mode, src_symbol),
            byte_diff: ByteQuantity::<i8>::from(src_byte_range.end - src_byte_range.start)
                - ByteQuantity(target.len() as i8),
            src_byte_range,
            target,
        });
    }
}

#[derive(Debug)]
struct Symbol {
    char_diff: CharQuantity<i8>,
    byte_diff: ByteQuantity<i8>,
    src_byte_range: Range<ByteQuantity<usize>>,
    target: String,
}

fn replace_symbols(tla_lines: &mut [TlaLine]) {
    for line_number in 0..tla_lines.len() - 1 {
        let (prefix, suffix) = tla_lines.split_at_mut(line_number + 1);
        let line = &mut prefix[line_number];
        while let Some(symbol) = line.symbols.pop() {
            let symbol_start_char_index = CharQuantity(
                line.text[ByteQuantity::<usize>::as_range_to(&symbol.src_byte_range.start)]
                    .chars()
                    .count(),
            );
            line.text.replace_range(
                ByteQuantity::as_range(&symbol.src_byte_range),
                &symbol.target,
            );
            line.shift(
                symbol.char_diff,
                symbol_start_char_index,
                symbol.byte_diff,
                symbol.src_byte_range.start,
            );
            fix_alignment(line, suffix, symbol.char_diff, symbol_start_char_index);
        }
    }
}

fn fix_alignment(
    line: &TlaLine,
    suffix: &mut [TlaLine],
    char_diff: CharQuantity<i8>,
    symbol_start_char_index: CharQuantity<usize>,
) {
    if char_diff == CharQuantity(0) {
        return;
    }
    for jlist in &line.jlists {
        if jlist.char_column <= symbol_start_char_index {
            continue;
        }
        for &offset in &jlist.bullet_line_offsets {
            if offset == 0 {
                continue;
            }
            let (suffix_prefix, suffix_suffix) = suffix.split_at_mut(offset);
            let bullet_line = &mut suffix_prefix[offset - 1];

            // Add or remove spaces from the start of the line
            // Since we are inserting ASCII spaces, byte_diff is equal to char_diff
            let byte_diff: ByteQuantity<i8> = char_diff.into();
            if byte_diff < ByteQuantity(0) {
                bullet_line
                    .text
                    .drain(ByteQuantity::<i8>::as_range_to(&(-byte_diff)));
            } else {
                bullet_line
                    .text
                    .insert_str(0, " ".repeat(char_diff.value() as usize).as_ref());
            }

            bullet_line.shift(char_diff, CharQuantity(0), byte_diff, ByteQuantity(0));

            // Recursively fix alignment of any jlists starting on this line
            fix_alignment(bullet_line, suffix_suffix, char_diff, CharQuantity(0));
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::iter::zip;

    fn check_ascii_replaced(text: &str) {
        let mut parser = Parser::new();
        parser
            .set_language(tree_sitter_tlaplus::language())
            .unwrap();
        let tree = parser.parse(&text, None).unwrap();
        assert!(!tree.root_node().has_error());
        let mut cursor = QueryCursor::new();
        let mappings = get_unicode_mappings().unwrap();
        let queries = &mappings
            .iter()
            .map(|s| s.ascii_query())
            .collect::<Vec<String>>()
            .join("");
        let query = Query::new(tree_sitter_tlaplus::language(), &queries).unwrap();
        assert_eq!(
            0,
            cursor
                .matches(&query, tree.root_node(), "".as_bytes())
                .count()
        );
    }

    fn unwrap_conversion(input: Result<String, TlaError>) -> String {
        match input {
            Ok(converted) => converted,
            Err(TlaError::InputFileParseError(tree)) => {
                panic!("{}", tree.root_node().to_sexp())
            }
            Err(TlaError::InvalidTranslationError {
                input_tree: _,
                output_tree: _,
                output,
            }) => {
                panic!("{}", output)
            }
        }
    }

    fn run_roundtrip_test(expected: String) {
        let intermediate = unwrap_conversion(rewrite(&expected, Mode::AsciiToUnicode, false));
        check_ascii_replaced(&intermediate);
        let actual = unwrap_conversion(rewrite(&intermediate, Mode::UnicodeToAscii, false));
        assert_eq!(expected, actual);
    }

    #[test]
    fn basic_roundtrip() {
        let expected = r#"---- MODULE Test ----
op == \A n \in Nat: n >= 0
===="#
            .to_string();
        run_roundtrip_test(expected);
    }

    #[test]
    fn all_canonical_symbols_roundtrip() {
        let expected = r#"---- MODULE Test ----
op == \A n \in Nat : \E r \in Real : ~(n = r)
op == {x \in R : TRUE}
op == INSTANCE Module WITH x <- y
op == [n \in Nat |-> n]
op == [Nat -> Real]
op == <<1,2,3>>
op == <<<>F>>_vars
op == CASE A -> B [] C -> D [] OTHER -> E
op == label :: []P => Q
op == A -+-> B \equiv C <=> D ~> E /\ F \/ G
op == A := B ::= C /= D <= E >= F \approx G
op == A |- B |= C -| D =| E \asymp F \cong G
op == A \doteq B \gg C \ll D \in E \notin F \prec G
op == A \succ B \preceq C \succeq D \propto E \sim F \simeq G
op == A \sqsubset B \sqsupset C \sqsubseteq D \sqsupseteq E
op == A \subset B \supset C \subseteq D \supseteq E
op == A \intersect B \union C .. D ... E (+) F (-) G
op == A || B (.) C (/) D (\X) E \bigcirc F \bullet G
op == A \div B \o C \star D !! E ?? F \sqcap G
op == A \sqcup B \uplus C \X D \wr E \cdot F ^+
===="#
            .to_string();
        run_roundtrip_test(expected);
    }

    #[test]
    fn all_non_canonical_symbols_roundtrip() {
        let expected = r#"---- MODULE Test ----
op == \forall n \in Nat : TRUE
op == \exists r \in Real : TRUE
op == \neg P
op == P \land Q
op == P \lor Q
op == x # y
op == x =< y
op == x \leq y
op == x \geq y
op == P \cap Q
op == P \cup Q
op == x \oplus y
op == x \ominus y
op == x \odot y
op == x \oslash y
op == x \otimes y
op == x \circ y
op == P \times Q
===="#
            .to_string();
        let intermediate = unwrap_conversion(rewrite(&expected, Mode::AsciiToUnicode, false));
        check_ascii_replaced(&intermediate);
        let actual = unwrap_conversion(rewrite(&intermediate, Mode::UnicodeToAscii, false));
        // Only first and last lines should be the same
        for (i, (expected_line, actual_line)) in zip(expected.lines(), actual.lines()).enumerate() {
            if i == 0 || i == expected.lines().count() - 1 {
                assert_eq!(expected_line, actual_line);
            } else {
                assert_ne!(expected_line, actual_line);
            }
        }
    }

    #[test]
    fn test_basic_jlist() {
        let expected = r#"---- MODULE Test ----
op == /\ A
      /\ B
      /\ C
      /\ D
===="#
            .to_string();
        run_roundtrip_test(expected);
    }

    #[test]
    fn test_nested_jlist() {
        let expected = r#"---- MODULE Test ----
op == /\ A
      /\ \/ B 
         \/ C
      /\ D
===="#
            .to_string();
        run_roundtrip_test(expected);
    }

    #[test]
    fn test_full_binary_tree_jlist() {
        let expected = r#"---- MODULE Test ----
op == /\ \/ /\ \/ /\ A
                  /\ B
               \/ /\ C
                  /\ D
            /\ \/ /\ E
                  /\ F
               \/ /\ G
                  /\ H
         \/ /\ \/ /\ I
                  /\ J
               \/ /\ K
                  /\ L
            /\ \/ /\ M
                  /\ N
               \/ /\ O
                  /\ P
      /\ \/ /\ \/ /\ Q
                  /\ R
               \/ /\ S
                  /\ T
            /\ \/ /\ U
                  /\ V
               \/ /\ W
                  /\ X
         \/ /\ \/ /\ Y
                  /\ Z
               \/ /\ A
                  /\ B
            /\ \/ /\ C
                  /\ D
               \/ /\ E
                  /\ F
===="#
            .to_string();
        run_roundtrip_test(expected);
    }

    #[test]
    fn jlist_with_comments() {
        let expected = r#"---- MODULE Test ----
op == /\ A
      /\ \/ B 
\* This is a comment
         \/ C
(* This is another comment *)
      /\ D
===="#
            .to_string();
        run_roundtrip_test(expected);
    }
}