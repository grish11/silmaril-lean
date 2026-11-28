# SQLite point-read compiler

The front end prepares one read-only statement of the form
`SELECT column FROM table WHERE rowid = ?1` against the Track D3 catalog
snapshot. Preparation yields D3's resolved target, projection label and
initially unset bind slot. The snapshot and session are inputs to preparation
and the prepared value carries no connection update.
[Track D handoff](sqlite-track-d/handoff-v1.md) ·
[D3 statement executor](sqlite-track-d/statement-executor.md)

## Text and planning boundary

| Component | Concrete state and operation | Abstract judgment and public theorem |
| --- | --- | --- |
| Tokenizer | A character suffix, scanned to a list of normalized tokens | `Lexes` specifies complete lexical coverage, including maximal word runs. `tokenize_iff` relates it to executable success. `lexes_render` relates canonical tokens to their text. [Header](../../Silmaril/Machine/SQLite/Tokenizer/Thms.lean) |
| Parser | A list of tokens and a two-name AST | `Grammar` specifies the complete stream and `parse_iff` characterizes success. `represents_print` takes a `Statement.WellFormed` hypothesis and gives a lexical and grammar witness for printed text. [Header](../../Silmaril/Machine/SQLite/Parser/Thms.lean) |
| Code Generator | A D3 connection, checked request and D3 prepared result | `Prepares` uses the D3 resolver relation. `prepare_iff` covers every planner outcome, including catalog rejection, missing names and the resolved plan with an empty binding. [Header](../../Silmaril/Machine/SQLite/CodeGenerator/Thms.lean) |
| SQL Command Processor | Text and a D3 connection | `parse_iff` and `parse_print` relate text to the AST. `prepare_iff` characterizes successful text preparation by composing text representation and catalog planning. [Header](../../Silmaril/Machine/SQLite/CommandProcessor/Thms.lean) |

The tokenizer works on Lean strings and consumes unquoted ASCII words starting
with a letter or underscore. It folds ASCII case before lookup, so supplied
catalog names must use D3's normalized spelling. It recognizes `=`, the exact
parameter `?1`, a semicolon and ASCII layout (space, tab, LF, CR, FF). The
grammar reserves `select`, `from` and `where`, requires the literal `rowid`
predicate and allows one optional final semicolon. Its printed form has a
space after every token. Quoted and qualified names, comments, other
parameters, literals, projection lists and further statements are outside
the fragment. The set of words accepted as names is defined by this model.
SQLite's complete keyword and identifier rules are outside the proof.

`CommandProcessor.invocation` supplies D3's `Invocation Names`, and
`CommandProcessor.request` delegates catalog admission to
`CatalogExecutor.classify`. Catalog rejection precedes resolution, including
for a view, a schema where `rowid` fails the D3 predicate check, or a generated
projection. A missing table or column in admitted scope becomes a D3
resolution error. Text rejected by the lexer or grammar has its own channel.
The fixtures check both channels, a mixed-case success with an empty binding,
two missing-name cases, and view and shadowed-rowid rejection.
[Checks](../../Silmaril/Machine/SQLite/CommandProcessor/Checks.lean)

## Bytecode and execution

The Interface consumer can call `CommandProcessor.prepare`, bind the returned
D3 value with `Prepared.bindInt64`, and pass it to `CodeGenerator.compile`
and `CodeGenerator.run`. The one-shot `CommandProcessor.execute` composes
text recognition, D3 admission and name resolution, optional binding, and
the compiled run. The unbound case yields the label and an empty result
without accessing the VM. A bound plan emits the existing VM's
`pointProgram` at the resolved zero-based column ordinal, the supplied
database and root, and the signed 64-bit key embedded as an immediate.
The program runs from `VirtualMachine.initial` with six steps of fuel.
[Compiler header](../../Silmaril/Machine/SQLite/CodeGenerator/Bytecode/Thms.lean) ·
[Execution header](../../Silmaril/Machine/SQLite/CommandProcessor/Execute/Thms.lean) ·
[VM header](../../Silmaril/Machine/SQLite/VirtualMachine/Thms.lean)

`CodeGenerator.Represents` requires the chosen location to contain a
VM table whose entry list matches the resolved D3 row list in order, by
signed rowid and the selected cell. The selected cell must be present
and cross D4's `Bridge.transferCell` with the exact D3 storage value.
Other columns are unobserved. This uses D4's UTF-8 encoding for decoded
text and rejection of NaN bit patterns. In particular, an absent
column in a short VM row cannot stand in for a present NULL. The caller
supplies the location and represented snapshot. For a fresh call
`Compatible` imposes that obligation only after admission, successful
resolution and a bind to slot one.

`CodeGenerator.run_compile` gives the label and D3 lookup result for a
represented, bound plan. Its hypothesis is vacuous when the plan is
unbound. `executeRequest_eq` gives the same D3 reply and full connection
as the D3 checked executor. With `Parser.Represents text stmt` and
`Compatible` for the catalog-classified invocation,
`CommandProcessor.execute_iff` relates the returned checked outcome
exactly to `CatalogExecutor.denote`. These outcomes include D3 scope
rejection, missing names, invalid bind indices, unbound execution,
misses, and hits, including a present NULL. Text rejection has its own
error. VM and transfer errors describe execution outside the theorem's
representation assumptions. In the pure D3 profile the catalog and
session are preserved, backing and cache are unit, and no exchanges
are observed.

The fixtures use a two-column table and project column one. A negative
key hits a present NULL, a positive key hits an integer, and another key
misses. An empty VM supplies no table on the unbound, resolution-error,
scope-rejection and bind-error paths. The checked short-row example
fails the representation and observes the VM's default NULL in place of
D3's integer. A missing VM table is a runtime fault. File/catalog
consistency, storage-backed execution, query optimization, general
SQLite grammar, the C handle lifecycle and native SQLite equivalence
are outside these results.
[Fixtures](../../Silmaril/Machine/SQLite/CommandProcessor/Execute/Checks.lean)

`CommandProcessor.pointRead_sat_iff_execute` composes this execution judgment
with a `CatalogPointRead` sentence. The same bound sentence can be evaluated
against each snapshot with the declared table schema. In each case, the text
must represent the declared names and the addressed VM table must represent
that snapshot's resolved projection.
[Query theorem](../../Silmaril/Machine/SQLite/CommandProcessor/Query/Thms.lean) ·
[Catalog sentences](relational-query-institutions.md#sqlite-point-reads)

## Upstream source and reproduction

The architecture diagram places the tokenizer, parser and code generator in
the SQL compiler. This model exposes a complete-input pipeline for the SQL
Command Processor. SQLite uses a push tokenizer and a Lemon parser. The
reference for the component boundaries is SQLite 3.54.1, split-source mirror
commit `57520227c95396ce39ba6ecaac8d475b78dd3964`.
[Architecture](https://www.sqlite.org/arch.html) ·
[Tokenizer](https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/tokenize.c) ·
[Grammar](https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/parse.y) ·
[Preparation](https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/prepare.c) ·
[SELECT](https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/select.c) ·
[WHERE](https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/where.c) ·
[VM opcodes](https://www.sqlite.org/opcode.html)

From the root with the repository's pinned toolchain:

```bash
lake build --wfail +Silmaril.Machine.SQLite.CommandProcessor.Checks \
  +Silmaril.Machine.SQLite.CommandProcessor.Execute.Checks
```
