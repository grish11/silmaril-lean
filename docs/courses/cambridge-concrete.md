# Cambridge L1 and L2 concrete syntax

`Silmaril.Courses.Cambridge.L1.Concrete` and
`Silmaril.Courses.Cambridge.L2.Concrete` parse UTF-8 source and print
canonical grouped bytes for Peter Sewell’s 12 February 2026 Part IB notes. The terms and types come from the collected
definitions in §§2.3 and 4.6. The concrete profiles also read ordinary
ungrouped input, including the L1 program on p. 13 and the curried L2
application on p. 49.
[Lecture notes](https://www.cl.cam.ac.uk/teaching/2526/Semantics/notes.pdf)

## Lexical conventions

- The parser decodes the complete byte array as UTF-8 and rejects malformed
  input. ASCII space, tab, carriage return and newline delimit tokens.
  Comments and Unicode whitespace are outside this profile.
- A maximal word consists of ASCII letters, digits, underscores or
  apostrophes. Variables begin with an ASCII letter or underscore.
  Keywords and locations are reserved. A location is `l` followed by zero or
  more digits, with the spelling kept verbatim. A numeral is a nonempty
  sequence of decimal digits, with no digit separators. A minus token before
  a numeral denotes a negative integer. Integers are unbounded.
- The lexer recognizes punctuation adjacent to other tokens. `>=`, `->`
  and `-` are aliases for `≥`, `→` and `−`. The pairs `:=`, `>=` and
  `->` are single tokens when adjacent.

## Grammar and binding

The parser consumes one complete expression or type. Parentheses group a
subexpression or a type without adding an AST node. Both languages use
`int`, `bool` and `unit`. L2 adds arrows. The `intref` notation describes
location typing judgments and has no expression type production.

From tightest to loosest, the expression levels are:

| Level | Binding |
| --- | --- |
| Atoms and `!location` | Dereference requires a location. A bare location is inadmissible as an expression. |
| Application (L2) | Left-associative juxtaposition. Group a compound keyword form such as a lambda when it follows a function as an argument. |
| `+` | One ungrouped addition per level. |
| `≥` | One ungrouped comparison per level. |
| `location := expression` | The target is a location. Assignment binds tighter than sequence. Group nested assignments. |
| `;` | Right-associative sequence. |

The notes state that application associates left, type arrows associate
right, and a lambda body extends as far right as delimiters permit (p. 49).
They mark `1 + 2 + 3` as ambiguous (p. 35). The remaining precedence table
is a parser convention, including the grouping requirement for chained
comparison, the relative binding of arithmetic and application, and the
association of sequence. The order of assignment and sequence agrees with
the opening L1 example (p. 13). The supplementary SML parser uses its
own concrete dialect, including `fn` and `let val`.
[Supplementary SML grammar](https://www.cl.cam.ac.uk/teaching/2526/Semantics/L2/Parser.grm)

Keyword forms can begin an operand. The test and arms of an `if` stop at
`then`, `else` and the enclosing delimiter. The nearest conditional consumes
its own `else`. A loop uses `do` and `done` to delimit its operands. The
value in a `let x : type = value in body` stops at `in`. The body extends to the
enclosing delimiter. For example, `x + let x:int = x in (x + 2)`
parses with the definition as the right operand (p. 60). In a lambda,
`fun x:int → int → x` gives the binder an arrow type and uses the last
arrow as the term delimiter. Parentheses can also mark the annotation
explicitly.

The course’s typed recursive form is
`let rec f : domain → codomain = (fun x : domain → body) in result`.
The repeated annotation must equal the parsed domain. The right-hand
side must be a parenthesized lambda. Other typing and store conditions
are checked separately.

L1 `parse` returns `L1.Expr`. L2 `parse` returns `L2.RawExpr`, with
binder spellings intact. L2 `parseResolved` applies the existing
`RawExpr.resolve []` and retains free names. An ordinary `let` binds in its
body. A recursive function name binds in the function and the `in` body,
and its parameter binds in the function body. De Bruijn indices and the
resolved free-variable constructor are internal representations. Store
configurations also have no source production.

## Canonical bytes and checks

`print` takes a `SourceExpr`, an AST with names in the source vocabulary.
The internal ASTs retain unrestricted strings. The printer emits fully
grouped compound terms, the Unicode symbols above and one ASCII space between
tokens. `parse_print` recovers the original AST and `print_injective` proves
that equal canonical bytes imply equal source ASTs. `parseType_printType`
and `printType_injective` give the corresponding contracts for expression
types. L2 also proves `parseResolved_print`. Parsing discards whitespace and
grouping choices.

The public parser tries the explicitly grouped reader first and the
precedence reader on a miss, both with a full-input check. The round-trip
theorems establish compatibility for the complete canonical printer
domain. L1 recursively restricts the shared L2 result to its imperative
fragment.

```sh
lake build --wfail +Silmaril.Courses.Cambridge.L1.Concrete \
  +Silmaril.Courses.Cambridge.L2.Concrete \
  +Silmaril.Courses.Cambridge.Concrete.Examples
```

[Byte regressions](../../Silmaril/Courses/Cambridge/Concrete/Examples.lean)
exercise both entry points on actual UTF-8 and malformed byte arrays. They
check grouping, associativity, token and binder boundaries, recursive
annotation agreement, canonically printed text and rejection of L2 forms
by L1.
