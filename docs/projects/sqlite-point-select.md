# SQLite point-read compiler front end

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

The prepared value exposes D3's `Prepared.bindInt64` for slot 1 and can be
passed to D3's snapshot executor. A caller combining prepare and execution
supplies the same catalog snapshot. This increment proves text and
preparation properties. Bytecode, query optimization, the C handle lifecycle,
storage-backed execution and native SQLite equivalence are outside its
theorems.

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
[WHERE](https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/where.c)

From the root with the repository's pinned toolchain:

```bash
lake build --wfail +Silmaril.Machine.SQLite.CommandProcessor.Checks
```
