## Overview

This program will take any ASCII TLA+ file and convert all its symbols to their Unicode equivalent, or take any Unicode TLA+ file and convert all its symbols to their ASCII equivalent.
The symbol mapping can be found in the [`./resources/tla-unicode.csv`](./resources/tla-unicode.csv) file.
TLA+ often has several ASCII symbols all representing the same operator (for example, `<=`, `=<`, and `\leq`); these will all map to the same Unicode symbol (`≤`), and when mapping back to ASCII the first ASCII symbol in the semicolon-separated CSV cell will be used (`<=`).
Users may use this tool to convert their old ASCII TLA+ files to use more easily-readable Unicode symbols, or to convert their Unicode TLA+ files to ASCII for tools which cannot yet handle Unicode.
The reason this program isn't just a simple search & replace is that blank space and column alignment matters for some TLA+ constructs, specifically conjunction and disjunction lists:

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

We see that both the conjunction and disjunction lists lost their alignment.
This is unlikely to change the logical value of the expression, but is still undesirable.
Thus we need to analyze the parse tree to find all conjunction & disjunction lists, and ensure our modifications do not change the alignments of their items.
For this purpose we use the TLA+ tree-sitter grammar, which correctly parses these constructs.
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

## Algorithm

The top-level algorithm is as follows:

1. For each line in the file, create two vectors: a jlist vector, and a symbol vector.
1. Use tree-sitter queries to identify the locations & scope of all conjunction and disjunction lists (henceforth referred to as "jlists"). For each line, push details of any jlists starting on that line onto the jlist vector, sorted from left to right.
1. Use tree-sitter queries to identify the locations of all symbols to be replaced.
Sort the symbol locations by line and then push them onto the symbol vector, with the rightmost symbol on top.
1. For each line, pop the symbol vector to get the rightmost remaining symbol.
If the symbol vector was empty, nothing needs to be done on this line.
Otherwise, replace the popped symbol.
If no jlists are to the right of this symbol, no further action is required; otherwise:
  1. For a given replaced symbol, it suffices to only consider the next-right jlist; iterate through the line's jlist vector to find it.
  1. For each subsequent line spanned by the next-right jlist, add or remove a space at the very beginning of the line to fix the alignment.
Update the positions of entities in the jlist and symbol stacks appropriately.

1. Once all symbol vectors are empty on all lines, the replacement process is complete; the symbols are all replaced, but the parse tree is unchanged.

