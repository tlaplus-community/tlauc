# TLAUC: The TLA⁺ Unicode Converter
[![Build & Test](https://github.com/tlaplus-community/tlauc/actions/workflows/ci.yml/badge.svg)](https://github.com/tlaplus-community/tlauc/actions/workflows/ci.yml)
[![crates.io](https://img.shields.io/crates/v/tlauc.svg)](https://crates.io/crates/tlauc)

Take the leap! Move from
```tla
S^+ == {e \in S : e > 0}
Infinitesimal == \A x \in Real^+: \E y \in Real^+: y < x
```
to
```tla
S⁺ ≜ {e ∈ S : e > 0}
Infinitesimal ≜ ∀ x ∈ ℝ⁺: ∃ y ∈ ℝ⁺: y < x
```

This package will take any ASCII TLA⁺ file and convert all its symbols to their Unicode equivalent, or take any Unicode TLA⁺ file and convert all its symbols to their ASCII equivalent.
It consists of two crates: a library exposing this functionality (using [tree-sitter-tlaplus](https://github.com/tlaplus-community/tree-sitter-tlaplus) under the hood), and a command line wrapper.

Use this tool to:
* Create a nice-looking copy of your spec that is pleasant to read but can still be edited and meaningfully tracked by source control
* Confidently write specs in Unicode with the [tlaplus-nvim-plugin](https://github.com/tlaplus-community/tlaplus-nvim-plugin) then output their ASCII equivalent to a temporary file for use with SANY and TLC
* Convert your existing ASCII specs to Unicode and use them with Unicode-aware tooling like [tla-web](https://github.com/will62794/tla-web)

Note that GitHub itself uses the tree-sitter-tlaplus grammar for highlighting, so it supports Unicode TLA⁺ as shown in the highlighted code snippets here.
If you want to check Unicode specs into source control and run non-Unicode-aware tooling like TLC during your CI process, you can add a step using this tool to translate your Unicode spec into TLC-supported form.

The symbol mapping can be found in the [`./resources/tla-unicode.csv`](./resources/tla-unicode.csv) file, taken from the [tlaplus-standard](https://github.com/tlaplus-community/tlaplus-standard) repo.
The crate also provides programmatic access to these mappings.
For an optimal TLA⁺ Unicode experience you'll want a monospace font that renders all these symbols in fixed width.

## Install & Use

This crate contains both a library and its command line wrapper.

To install the command line tool:
1. Install rust: https://www.rust-lang.org/tools/install
1. Run `cargo install tlauc`
1. Ensure the [cargo installation directory](https://doc.rust-lang.org/cargo/commands/cargo-install.html#description) is on your path

From the command line, convert a TLA⁺ file from ASCII to Unicode as follows:
```sh
tlauc unicode --input Ascii.tla --output Unicode.tla
```
Convert from Unicode to ASCII:
```sh
tlauc ascii --input Unicode.tla --output Ascii.tla
```
By default, the program will fail if a file exists at the output location; override this behavior with the `--overwrite` flag.
There are also several safety checks performed during the translation process, like that the input spec parses correctly and that the output spec has the same parse tree as the input spec.
You can override these safety checks with the `-f` or `--force` flag, which also sets the `--overwrite` flag.

To consume the library, add [the tlauc package](https://crates.io/crates/tlauc) as a dependency of your project then use it as follows:
```rs
use tlauc::{rewrite, Mode};

fn main() {
    let input = r#"---- MODULE TotalOrder ----
EXTENDS Reals

Reflexive(S) == \A a \in S : a <= a
Transitive(S) == \A a, b, c \in S : (a <= b /\ b <= c) => (a <= c)
Antisymmetric(S) == \A a, b \in S : (a <= b /\ a >= b) => (a = b)
Total(S) == \A a, b \in S : a <= b \/ a >= b
IsTotallyOrdered(S) ==
    /\ Reflexive(S)
    /\ Transitive(S)
    /\ Antisymmetric(S)
    /\ Rotal(S)
THEOREM RealsTotallyOrdered == IsTotallyOrdered(Real)
===="#;
    println!("{}", rewrite(input, Mode::AsciiToUnicode, false).unwrap());
}
```
which will output:
```tla
---- MODULE TotalOrder ----
EXTENDS Reals

Reflexive(S) ≜ ∀ a ∈ S : a ≤ a
Transitive(S) ≜ ∀ a, b, c ∈ S : (a ≤ b ∧ b ≤ c) ⇒ (a ≤ c)
Antisymmetric(S) ≜ ∀ a, b ∈ S : (a ≤ b ∧ a ≥ b) ⇒ (a = b)
Total(S) ≜ ∀ a, b ∈ S : a ≤ b ∨ a ≥ b
IsTotallyOrdered(S) ≜
    ∧ Reflexive(S)
    ∧ Transitive(S)
    ∧ Antisymmetric(S)
    ∧ Total(S)
THEOREM RealsTotallyOrdered ≜ IsTotallyOrdered(ℝ)
====
```
Details of reading & writing files are left to the user, but you can look at the command line wrapper for a detailed example.

Access the list of Unicode mappings as follows:
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

TLA⁺ often has several ASCII symbols all representing the same operator (for example, `<=`, `=<`, and `\leq`); these will all map to the same Unicode symbol (`≤`), and when mapping back to ASCII the first ASCII symbol in the semicolon-separated CSV cell will be used (`<=`).

The reason this program isn't just a simple search & replace is that blank space and column alignment matters for some TLA⁺ constructs, specifically conjunction and disjunction lists (henceforth called jlists):

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

```sexp
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
For safety, the program checks to ensure the converted TLA⁺ file has the exact same parse tree as the original.
It also will not convert the input file if it contains any parse errors.
Both of these checks can be bypassed with the `--force` command line parameter (also exposed in the library).

## Algorithm

The high-level conversion algorithm is as follows:

1. For each line in the input file, create two vectors: a jlist vector, and a symbol vector.
1. Parse the input file and use tree-sitter queries to identify the locations & scope of all jlists.
For each line, push details of any jlists starting on that line onto the jlist vector, sorted from left to right.
1. Use tree-sitter queries to identify the locations of all symbols to be replaced.
Sort the symbol locations by line and then push them onto the line's symbol vector, sorted from left to right.
1. For each line, iteratively pop the top element off the symbol vector and replace it in the text.
If no jlists start to the right of that symbol the line, no further action is required; otherwise:
   1. For each jlist starting to the right of the replaced symbol on that line, iterate through all subsequent bullet lines and add or remove spaces to fix the alignment.
   Update the positions of entities in the jlist and symbol stacks on those lines.
   1. For each jlist bullet alignment fixed, check whether any additional jlists start on that line; recursively fix their alignment with the same process until no jlists remain to be fixed.

1. After iterating through all lines, the process is complete; parse the converted tree and compare it to the original.
They should be identical.

## Complications

As always with variable-width UTF-8 encoded text, care must be taken to differentiate the byte index of a symbol (henceforth called a "codepoint") from its character index.
We [long ago](https://www.joelonsoftware.com/2003/10/08/the-absolute-minimum-every-software-developer-absolutely-positively-must-know-about-unicode-and-character-sets-no-excuses/) left the world of "plain text = ASCII = characters are 1 byte".
Now, each "character" is really a codepoint (an arbitrarily-large number identifying a symbol in the international Unicode standard) that can be 1 byte (as all the ASCII-equivalent codepoints remain, for seamless backward compatibility) or 2 bytes, or 3, 4, etc.
Fundamentally this means that given a byte index, you can't know a codepoint's character index (here also called its "displayed" index) without reading from the beginning of whatever line you are on and counting how many codepoints you encounter.
This complexity is of particular concern for this project, which involves a lot of maintaining text alignment, shifting, inserting Unicode symbols, and index arithmetic.
Rust's type system proved very helpful here; instead of storing indices or offsets as primitive types like `usize` or `i8`, a number of wrapper types were defined to enforce index arithmetic safety at the type-checking level.
You can only add or compare values of like types, and converting from one type to the other requires reading the indexed line of text from the beginning.
At the expense of some additional verbiage this greatly reduced the difficulty of keeping character and byte indices separate and reasoning about when it is appropriate to use each.
For possible (but unlikely) future work there is even more complexity to be found with modifier codepoints, where multiple codepoints combine to form one "grapheme cluster" (what we would think of as a "character" in the ASCII world); for example, the grapheme cluster `é` can either be written directly as codepoint `U+00E9` or as codepoints `U+0301 U+0065`, where `U+0301` is the accent modifier ("combining diacritical mark") applied to `U+0065`, which is our familiar ASCII-equivalent code for `e`.
This program does not handle grapheme clusters and (wrongly, but conveniently) assumes one codepoint = one displayed character.
This would only ever be an issue if someone were to use modifiers in comments prepending alignment-sensitive syntax (see below), which is such a niche use case that for simplicity it will not be handled at this time.

For actual syntax processing, the most troublesome edge case is as follows:
```tla
op == /\ A
      /\ B
      => C
```
When converting from ASCII to Unicode using the naive algorithm, this results in:
```tla
op ≜ ∧ A
     ∧ B
      ⇒ C
```
So this changes `(A ∧ B) ⇒ C` into `A ∧ (B ⇒ C)`, absolutely a different logical expression.
The solution to this edge case is to look for infix operator nodes that are the parent of jlist nodes where the jlist is the left-hand expression.
Thankfully this is easily done with the tree-sitter query `(bound_infix_op lhs: [(conj_list) (disj_list)]) @capture`.
Then, record the operator symbol column offset relative to the jlist column, and maintain it as much as possible as the jlist is shifted.
The edge case is also present in the other direction when converting from Unicode to ASCII:
```tla
op ≜ ∧ A
     ∧ B
      = C
     ∧ D
      = E
```
Which converts to:
```tla
op == /\ A
      /\ B
      = C
      /\ D
      = E
```
So `(A ∧ (B = C)) ∧ (D = E)` is changed to `((A ∧ B) = C) ∧ D) = E`.
This direction is substantially more difficult to detect via tree-sitter queries, since `B = C` can be an arbitrarily-long and complicated expression that eventually spills onto additional lines.
Since this scenario is very unlikely to occur in the wild until large numbers of TLA⁺ specs are being written in Unicode first, this case is not currently handled by the program (see issue https://github.com/tlaplus-community/tlauc/issues/1).

Another edge case involves block comments in the (usually empty) space before jlist items:
```tla
op == /\ A
(***) /\ B
(***) /\ C
```
If one or more comments are present in this way they function as hard constraints on how much the jlist can be shifted to the left.
This turns jlist shifting from a simple greedy algorithm into more of a constraint satisfaction problem, especially once nested jlists are involved or even combined with the infix operator edge case up above, forming a tricky corner case:
```tla
op == /\ A
(***) /\ \/ B
(******) \/ C
(***) => D
```
Note also that comments can include arbitrary Unicode symbols so care must be taken to use character indices instead of byte indices for column alignment (see discussion of Unicode difficulties above).
Of course this means the jlists will not be aligned in non-Unicode-aware tooling, but that is the concern of the user; this tool does not modify comment text.
It really only seems feasible to assume one codepoint = one displayed character; alignment according to grapheme clusters would add unnecessary complication to a very niche use case.

The block comment edge case has not been observed in the wild and so is not yet supported; see issue https://github.com/tlaplus-community/tlauc/issues/2.

## Prior Art

[Ron Pressler](https://pron.github.io/) did some work ([link](https://github.com/pron/tlaplus/tree/unicode-presentation-2/tlatools/src/tla2unicode)) in early 2017 trying to add Unicode support to SANY, which faced many of the same challenges around jlist alignment.

