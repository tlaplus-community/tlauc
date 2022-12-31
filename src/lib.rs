mod strquantity;
use crate::strquantity::{ByteQuantity, CharQuantity};

use serde::{Deserialize, Deserializer};
use std::ops::Range;
use tree_sitter::{Parser, Point, Query, QueryCursor, Tree, TreeCursor};

pub enum Mode {
    AsciiToUnicode,
    UnicodeToAscii,
}

#[derive(Debug)]
pub enum TlaError {
    InputFileParseError(Tree),
    OutputFileParseError(Tree),
    InvalidTranslationError {
        input_tree: Tree,
        output_tree: Tree,
        output: String,
        first_diff: String,
    },
}

pub fn rewrite(input: &str, mode: &Mode, force: bool) -> Result<String, TlaError> {
    let mut parser = Parser::new();
    parser
        .set_language(tree_sitter_tlaplus::language())
        .expect("Error loading TLA⁺ grammar");
    let mut cursor = QueryCursor::new();
    //
    // Parse input TLA⁺ file and construct data structures to hold information about it
    let input_tree = parser.parse(input, None).unwrap();
    if !force && input_tree.root_node().has_error() {
        return Err(TlaError::InputFileParseError(input_tree));
    }

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
    if !force {
        if output_tree.root_node().has_error() {
            return Err(TlaError::OutputFileParseError(output_tree));
        }
        if let Err(first_diff) = compare_parse_trees(&input_tree, &output_tree) {
            return Err(TlaError::InvalidTranslationError {
                input_tree,
                output_tree,
                output,
                first_diff,
            });
        }
    }

    Ok(output)
}

fn compare_parse_trees(input_tree: &Tree, output_tree: &Tree) -> Result<(), String> {
    let mut input_cursor: TreeCursor = input_tree.walk();
    let mut output_cursor: TreeCursor = output_tree.walk();

    loop {
        check_node_equality(&input_cursor, &output_cursor)?;
        if !simultaneous_step(&mut input_cursor, &mut output_cursor, |c| {
            c.goto_first_child()
        })? {
            loop {
                if !simultaneous_step(&mut input_cursor, &mut output_cursor, |c| {
                    c.goto_next_sibling()
                })? {
                    if !simultaneous_step(&mut input_cursor, &mut output_cursor, |c| {
                        c.goto_parent()
                    })? {
                        return Ok(());
                    }
                } else {
                    break;
                }
            }
        }
    }
}

fn simultaneous_step(
    input_cursor: &mut TreeCursor,
    output_cursor: &mut TreeCursor,
    step: fn(&mut TreeCursor) -> bool,
) -> Result<bool, String> {
    let (input_next, output_next) = (step(input_cursor), step(output_cursor));
    if input_next != output_next {
        return Err(format!(
            "First diff: Input {:?} Output {:?}",
            input_cursor.node(),
            output_cursor.node()
        ));
    }

    Ok(input_next)
}

fn check_node_equality(
    input_cursor: &TreeCursor,
    output_cursor: &TreeCursor,
) -> Result<(), String> {
    if (input_cursor.node().is_named() || output_cursor.node().is_named())
        && input_cursor.node().kind() != output_cursor.node().kind()
    {
        return Err(format!(
            "First diff: Input {:?} Output {:?}",
            input_cursor.node(),
            output_cursor.node()
        ));
    }

    Ok(())
}

#[derive(Debug, Deserialize)]
pub struct SymbolMapping {
    #[serde(rename = "Name")]
    name: String,
    #[serde(
        rename = "ASCII",
        deserialize_with = "vec_from_semicolon_separated_str"
    )]
    ascii: Vec<String>,
    #[serde(rename = "Unicode")]
    unicode: String,
}

impl SymbolMapping {
    pub fn canonical_ascii(&self) -> &str {
        self.ascii.first().unwrap()
    }

    pub fn ascii_query(&self) -> String {
        let query = self
            .ascii
            .iter()
            .map(|a| a.replace('\\', "\\\\"))
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

fn vec_from_semicolon_separated_str<'de, D>(deserializer: D) -> Result<Vec<String>, D::Error>
where
    D: Deserializer<'de>,
{
    let s: &str = Deserialize::deserialize(deserializer)?;
    Ok(s.split(';').map(|s| s.to_string()).collect())
}

pub fn get_unicode_mappings() -> Vec<SymbolMapping> {
    let csv = include_str!("../resources/tla-unicode.csv");
    let mut reader = csv::Reader::from_reader(csv.as_bytes());
    reader.deserialize().map(|result| result.unwrap()).collect()
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

#[derive(Debug)]
struct JList {
    char_column: CharQuantity<usize>,
    bullet_line_offsets: Vec<usize>,
    terminating_infix_op_offset: Option<Point>,
}

impl JList {
    fn query() -> Query {
        Query::new(
            tree_sitter_tlaplus::language(),
            "[(conj_list) (disj_list)] @jlist",
        )
        .unwrap()
    }

    fn terminating_infix_op_query() -> Query {
        Query::new(
            tree_sitter_tlaplus::language(),
            "bound_infix_op lhs: [(conj_list) (disj_list)]) @capture"
        )
        .unwrap()
    }

    fn is_jlist_item_node(cursor: &TreeCursor) -> bool {
        "conj_item" == cursor.node().kind() || "disj_item" == cursor.node().kind()
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
            terminating_infix_op_offset: None,
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

    for capture in query_cursor.matches(&JList::terminating_infix_op_query(), tree.root_node(), "".as_bytes()) {
        let infix_op_node = capture.captures[0].node;
        let start_line = infix_op_node.start_position().row;
        let line = &mut tla_lines[start_line];
        let jlist_node = infix_op_node.child_by_field_name("lhs").unwrap();
        //let jlist = line.jlists.next(|j| j.column == jlist_node.start_position().column).unwrap();
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

fn mark_symbols(tree: &Tree, cursor: &mut QueryCursor, tla_lines: &mut [TlaLine], mode: &Mode) {
    let mappings = get_unicode_mappings();
    let queries = &mappings
        .iter()
        .map(|s| s.source_query(mode))
        .collect::<Vec<String>>()
        .join("");
    let query = Query::new(tree_sitter_tlaplus::language(), queries).unwrap();

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
        let queries = get_unicode_mappings()
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
            Err(TlaError::OutputFileParseError(tree)) => {
                panic!("{}", tree.root_node().to_sexp())
            }
            Err(TlaError::InvalidTranslationError {
                input_tree: _,
                output_tree: _,
                output: _,
                first_diff,
            }) => {
                panic!("{}", first_diff)
            }
        }
    }

    fn run_roundtrip_test(expected: &str) {
        let intermediate = unwrap_conversion(rewrite(expected, &Mode::AsciiToUnicode, false));
        check_ascii_replaced(&intermediate);
        let actual = unwrap_conversion(rewrite(&intermediate, &Mode::UnicodeToAscii, false));
        assert_eq!(expected, actual);
    }

    #[test]
    fn basic_roundtrip() {
        run_roundtrip_test(
            r#"---- MODULE Test ----
op == \A n \in Nat: n >= 0
===="#,
        );
    }

    #[test]
    fn all_canonical_symbols_roundtrip() {
        run_roundtrip_test(
            r#"---- MODULE Test ----
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
===="#,
        );
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
===="#;
        let intermediate = unwrap_conversion(rewrite(expected, &Mode::AsciiToUnicode, false));
        check_ascii_replaced(&intermediate);
        let actual = unwrap_conversion(rewrite(&intermediate, &Mode::UnicodeToAscii, false));
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
        run_roundtrip_test(
            r#"---- MODULE Test ----
op == /\ A
      /\ B
      /\ C
      /\ D
===="#,
        );
    }

    #[test]
    fn test_nested_jlist() {
        run_roundtrip_test(
            r#"---- MODULE Test ----
op == /\ A
      /\ \/ B 
         \/ C
      /\ D
===="#,
        );
    }

    #[test]
    fn test_full_binary_tree_jlist() {
        run_roundtrip_test(
            r#"---- MODULE Test ----
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
===="#,
        );
    }

    #[test]
    fn jlist_with_comments() {
        run_roundtrip_test(
            r#"---- MODULE Test ----
op == /\ A
      /\ \/ B 
\* This is a comment
         \/ C
(* This is another comment *)
      /\ D
===="#,
        );
    }

    #[ignore]
    #[test]
    fn test_infix_op_edge_case() {
        run_roundtrip_test(
            r#"---- MODULE Test ----
op == /\ A
      /\ B
      => C
===="#,
        );
    }

    #[ignore]
    #[test]
    fn test_misaligned_jlist_edge_case() {
        run_roundtrip_test(
            r#"---- MODULE Test ----
op == /\ A
     /\ B
     /\ C
===="#,
        );
    }
}
