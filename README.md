# TLAUC: The TLA+ Unicode Converter
[![Build & Test](https://github.com/tlaplus-community/tlauc/actions/workflows/ci.yml/badge.svg)](https://github.com/tlaplus-community/tlauc/actions/workflows/ci.yml)

## Overview

This crate will take any ASCII TLA+ file and convert all its symbols to their Unicode equivalent, or take any Unicode TLA+ file and convert all its symbols to their ASCII equivalent.
The symbol mapping can be found in the [`./resources/tla-unicode.csv`](./resources/tla-unicode.csv) file, taken from the [tlaplus-standard](https://github.com/tlaplus-community/tlaplus-standard) repo.
The crate also provides programmatic access to these mappings.

## Use

This crate contains both a library and its command line wrapper.

Consume the library from your own code as follows:
```rs
use tlauc::{rewrite, Mode};

fn main() {
    let input = r#"---- MODULE Test ----
op == \A r1 \in Real : \E r2 \in Real : r2 < r1
===="#;
    println!("{}", rewrite(input, Mode::AsciiToUnicode, false).unwrap());
}
```
which will output:
```tla
---- MODULE Test ----
op ≜ ∀ r1 ∈ ℝ : ∃ r2 ∈ ℝ : r2 < r1
====
```
Details of reading & writing files are left to the user.

Access the list of unicode mappings as follows:
```rs
use tlauc::{SymbolMapping, get_unicode_mappings};

fn main() {
    let mappings: Vec<SymbolMapping> = get_unicode_mappings();
    println!("{:#?}", mappings);
}
```

## Build & Test

1. Install Rust: https://www.rust-lang.org/tools/install
1. Clone repo with the `--recurse-submodules` parameter
1. Run `cargo build`
1. Run `cargo test`

## Details

TLA+ often has several ASCII symbols all representing the same operator (for example, `<=`, `=<`, and `\leq`); these will all map to the same Unicode symbol (`≤`), and when mapping back to ASCII the first ASCII symbol in the semicolon-separated CSV cell will be used (`<=`).
Users may use this tool to convert their old ASCII TLA+ files to more-easily-read Unicode symbols, or convert their Unicode TLA+ files to ASCII for tools which cannot yet handle Unicode.

The reason this program isn't just a simple search & replace is that blank space and column alignment matters for some TLA+ constructs, specifically conjunction and disjunction lists (henceforth called jlists):

```tla
def == /\ A
       /\ \/ B
          \/ C
       /\ D
```

If we were to naively replace every ASCII symbol with their Unicode
equivalent, we would end up with:

```tla
def ≜ ∧ A
       ∧ ∨ B
          ∨ C
       ∧ D
```

We see that both the jlists lost their alignment.
This is unlikely to change the logical value of the expression, but is still undesirable.
Thus we need to analyze the parse tree to find all jlists, and ensure our modifications maintain the alignments of their items.
For this purpose we use [tree-sitter-tlaplus](https://github.com/tlaplus-community/tree-sitter-tlaplus), which correctly parses these constructs.
The tree-sitter parse tree for the above (correctly aligned) code snippet is:

```lisp
(operator_definition (identifier) (def_eq)
  (conj_list
    (conj_item (bullet_conj) (identifier_ref))
    (conj_item
      (bullet_conj)
      (disj_list
        (disj_item (bullet_disj) (identifier_ref))
        (disj_item (bullet_disj) (identifier_ref))
      )
    )
    (conj_item (bullet_conj) (identifier_ref))
  )
)
```
Note that for an optimal TLA+ unicode experience, you need a monospace font that renders all the relevant unicode math symbols in fixed width.
Without this feature, displayed jlist alignment may differ from actual jlist alignment.

For safety, the program checks to ensure the converted TLA+ file has the exact same parse tree as the original.
It also will not convert the input file if it contains any parse errors.
Both of these checks can be bypassed with the `--force` command line parameter (also exposed in the library).

## Algorithm

The high-level algorithm is as follows:

1. For each line in the input file, create two vectors: a jlist vector, and a symbol vector.
1. Parse the input file and use tree-sitter queries to identify the locations & scope of all jlists.
For each line, push details of any jlists starting on that line onto the jlist vector, sorted from left to right.
1. Use tree-sitter queries to identify the locations of all symbols to be replaced.
Sort the symbol locations by line and then push them onto the line's symbol vector, sorted from left to right.
1. For each line, iteratively pop the top element off the symbol vector and replace it in the text.
If no jlists start to the right of that symbol the line, no further action is required; otherwise:
   1. For each jlist starting to the right of the replaced symbol on that line, iterate through all subsequent bullet lines and add or remove space at the beginning of the line to fix the alignment.
   Update the positions of entities in the jlist and symbol stacks on those lines.
   1. For each jlist bullet alignment fixed, check whether any additional jlists start on that line; recursively fix their alignment with the same process until no jlists remain to be fixed.

1. After iterating through all lines, the process is complete; parse the converted tree and compare it to the original.
They should be identical.
