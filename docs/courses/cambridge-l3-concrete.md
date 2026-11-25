# Cambridge L3 concrete syntax

Import `Silmaril.Courses.Cambridge.L3.Concrete` to parse and print L3 terms
and types from Peter Sewell’s 12 February 2026 notes. The byte profile covers
the constructors of the collected definition and extends the
[L1/L2 UTF-8 and precedence rules](cambridge-concrete.md). Application
associates left, arrows associate right, and lambda bodies extend to the
enclosing delimiter as in L2.
[Sewell, pp. 49, 69–75 and 78–82](https://www.cl.cam.ac.uk/teaching/2526/Semantics/notes.pdf)

## Terms and types

The tightest term levels are atom, prefix operators (`!`, `ref`, `fst`,
`snd`), field projection and application, in that order. Projections chain
on the left, so `r.p.q` means `(r.p).q`. Group an operand to change the
binding. For example, `fst (r.p)` applies `fst` to the field. The precedence of
prefix operators over projection preserves the existing grouped spelling
of `(fst r . p)` as a projection. The notes leave the relative binding of
these operators open.

Addition, comparison, assignment and sequence have the same levels as in
L1/L2. L3 accepts an expression as the assignment target and as the operand
of dereference. Parentheses are part of pair notation `(left, right)`.
A pair may contain compound ungrouped operands and nesting requires a
separate pair at each level. The comma also separates fields within braces.

An injection has the form `inl term : type` or `inr term : type`. The colon
ends the payload and introduces a full type. A match uses
`match term with inl (x : type) → left | inr (y : type) → right`.
The branch binder parentheses and the bar delimit the annotated binders
and the first branch. The final branch extends to the enclosing delimiter.
Group an injection or match when using the whole expression as an
application argument. The binding of these forms next to other operators
is a parser convention.

Type precedence, from tightest to loosest, is atom (including records),
postfix `ref`, product `∗`, sum `+`, and arrow `→`. Postfix `ref` may repeat.
An unparenthesized product chain such as `int ∗ int ∗ int` is excluded by
the notes (p. 69). This parser also requires grouping for nested sums.
The relative levels for products, sums and references, and the grouping
requirement for nested sums, are parser conventions.

Each field list can be empty. Nonempty lists are comma-separated, with
distinct labels and no trailing comma. The parser preserves order and builds
the course AST’s `RecordLabels` witness. In `let rec`, the two parameter
type annotations must agree as parsed types, including the order of any
record fields. `*` is an ASCII alias for `∗`.

Variables and labels use the existing ASCII identifier spelling and
are distinguished by grammatical position. The notes distinguish their
sets and use distinct label metavariables. The parser does not partition
identifier spellings into two lexicons, so `x` can spell a label in a field
position and a variable in a term position. L3 additionally reserves
`fst`, `snd`, `ref`, `inl`, `inr`, `match` and `with`. Earlier languages
still allow these names.
The AST numbers the notes’ locations in the order `l`, `l0`, `l1`, and so on.
Numeric location suffixes use decimal without leading zeros. The term grammar
can read these literals. The separate course convention that whole programs
start with an empty store and create their own locations concerns execution.

## AST and byte contracts

`parse` returns the course’s named `L3.RawExpr`. `parseResolved` uses the
existing resolver, including independent payload binders in the two match
branches. De Bruijn indices and store configurations belong to the internal
model. `parseType` returns `L3.Ty`. The parsers consume the complete input.
Semantic typing and store invariants are still checked by the course
interfaces.

The public parser tries the explicitly grouped reader first and uses the
precedence reader on a miss. Both require complete input. The canonical
printers take `SourceExpr` or `SourceType`, whose names have a spelling in
the source vocabulary. They preserve record order and all
binder names. `parse_print` and `parseType_printType` recover the original
ASTs. `print_injective` and `printType_injective` follow from those
round-trips. `parseResolved_print` gives the corresponding resolved
expression.

```sh
lake build --wfail +Silmaril.Courses.Cambridge.L3.Concrete \
  +Silmaril.Courses.Cambridge.L3.Concrete.Examples
```

The [byte regressions](../../Silmaril/Courses/Cambridge/L3/Concrete/Examples.lean)
cover ordered records, duplicate labels, grouped products, precedence and
association, annotation and match boundaries, scope resolution, mutation
and allocation, canonical printing and malformed input.
