# Python source syntax and function scope

Use [Source.Syntax.Defs](../../Silmaril/Languages/Python/Source/Syntax/Defs.lean)
for unresolved constructor data and
[Source.Scope.Thms](../../Silmaril/Languages/Python/Source/Scope/Thms.lean)
for executable analysis and its enclosing-binder law. The source fragment
covers modules, classes, nested functions and lambdas with parameter kinds
and defaults, assignment and deletion targets, declarations,
selective imports, and conditional, loop and exception suites.

`analyze` collects name occurrences and declarations before resolving each
block. A name assigned later in a function is local throughout that block.
A default expression is read in the block defining the function.
Nested functions refer to captured names by stable paths. Each defining
function reports its cells, and intervening functions report the captures
they forward. The module and explicit global declarations are enclosing
lookup barriers. An unbound `nonlocal`, a declaration following a use or
binding, and a parameter/declaration collision produce distinct diagnostics.
The default policy rejects an unresolved `nonlocal`. Reference comparisons
can select `.globalFallback` to resolve only that case as implicit global
access. A found enclosing binding still takes precedence, and the module
scope check still applies.

Each block also exposes name occurrences in traversal order, including
repeated uses. An occurrence is addressed by the block path and its ordinal.
Each entry carries its usage, resolved access and a proof that looking up
the same name in that block returns that access.

`collectLexical` exposes the source-collected block tree and its ordered
name occurrences. `inferLexical` resolves that tree and certifies that
`ScopeTree.lexical` recovers it exactly. The
`analyze_preserves_lexical` theorem gives the same guarantee through
the combined entry point, including block metadata and sibling order.

Class bases are read in the enclosing block. Class bodies distinguish
namespace lookup from free access to an enclosing cell. Method lookup skips
the ordinary class namespace, including its global declarations, while
functions referring to the synthetic `__class__` cell capture their enclosing
class. A use of `super` within a function adds the implicit `__class__` use.

Lambda bodies have function scope and leave the enclosing namespace
untouched. Defaults, decorators, class bases and class keyword values
are visited in the defining block. Child paths follow traversal order.
Function defaults precede annotations and decorators. Class decorators
precede bases and keyword values. The caller selects eager or deferred
annotation traversal. Lambda parameter annotations are rejected.

Each collected block records whether its own lexical traversal visited a
`yield` expression, including in an unreachable branch. Nested function
and lambda bodies record their own yields. A yield in a nested function's
default belongs to the defining block. This metadata is available for
generator detection independently of the rules for generator execution.

Destructuring and loop targets bind their names in the current block.
Attribute and subscript targets read their operands. Exception-handler
targets and selective import aliases also bind in the current block.
Star imports report an explicit diagnostic because their bindings would
depend on a runtime module.

Expression syntax retains collections, comparison chains, slices, yield
operands and call argument forms. Text literals carry code points, including
lone surrogates. Floating literals carry binary64 bits. Scope visits all
dictionary keys before values. The constructor profile reports unsupported
comprehensions, generator expressions and bytes literals explicitly.

`enclosingBinding_eq_some_iff` characterizes successful executable lookup
with an inductive nearest-binder judgment. `enclosingBinding_stops`
characterizes lookup at a barrier. The regression exercises the full
constructor-to-scope path, including shadowing, forwarding through a function
with no direct use, default scope, and rejected declarations.

The scope profile follows Python 3.7 lexical binding and declaration rules.
Deleting a name counts as binding it for scope analysis. This entry point
accepts constructor data and checks the represented scope rules. Full syntax
validation, compilation, and runtime name lookup have separate contracts.

## Closure layout

The [closure layout checker](../../Silmaril/Languages/Python/Source/Closure/Thms.lean)
looks up a child's captures in a selected parent scope. An owned capture
contains a bounded index into the parent's cells. A forwarded capture
contains a bounded index into the parent's incoming captures. The slot
witness records the lexical origin and the name or capture found at that
index. The output follows the child's capture order.
`Layout.cells` reads the child's ordered cell identities from the chosen
parent slots, with its length certified against the child's capture vector.

The checker succeeds exactly when every capture is available in its
corresponding parent slot family. The regression analyzes three nested
functions and checks their interleaved owned and forwarded slots. It
also checks rejection when the selected scope lacks a required slot.

The [source frame layout](../../Silmaril/Languages/Python/Source/Closure/Frame/Thms.lean)
lists ordinary local names separately from owned cells and forwarded
captures. The parameter checker emits distinct, bounded local-or-owned
destinations. Mapping destination names back gives the original parameter
order. The capture entries are also available as a vector indexed by the
child's capture count.

The [Core lowering](../../Silmaril/Languages/Python/Compile/Closure/Thms.lean)
assigns distinct slot families to ordinary locals, owned cells and forwarded
captures. Parameter destinations keep declaration order. A nested closure
selects the same parent cell identity at each capture index as the source
layout. The regression constructs both versions of the Core closure and
reads a parent's subsequent write through the child's capture.

The [closure body compiler](../../Silmaril/Languages/Python/Compile/Closure/Body/Thms.lean)
accepts one top-level function containing nested function definitions,
single-name assignments and nonlocal declarations, with a final value return
in each function. Expressions cover integers, addition, names and positional
calls. Each successful result carries the analyzed source tree and a
translation derivation. Child code carries the analyzed path, ordered
parameter destinations and capture operands. The compiler proves its
preorder list of code paths has no duplicates for code-table linking. The
regression parses Python source and checks a nonlocal write through two
nested call sites. Code-table linking and execution are subsequent stages.

## Source intake

The AST emitter takes an external CPython AST and writes a Lean module
defining `pythonSource`. It runs under Python 3.10 or later and requests
`feature_version=(3, 7)`. That option uses the host parser's best-effort
grammar profile. The scope proofs begin at the Lean constructors.

```sh
python3 -I tools/python-source/source_ast.py example.py --output /tmp/Example.lean
lake env lean -DwarningAsError=true /tmp/Example.lean
```

The emitter preserves source text as code points and floating literals as
the host AST's binary64 bits. Constructors for known unsupported forms
remain visible to Lean's scope diagnostics. Other unsupported nodes
produce an error before an output file is written. The intake regression
feeds actual Python through the emitter and runs scope checks on the
resulting Lean constructors.

```sh
make check CHECK_TARGETS=+Silmaril.Languages.Python.Source.Scope.Thms
```

- Python 3.7.17, §4.2, SHA-256
  `2fff14c12f27e67e029528cdb3c2de6f0c499759d7ce33584731f50f5daffada`.
  [Execution model](https://docs.python.org/release/3.7.17/reference/executionmodel.html#naming-and-binding)
- Python 3.7.17, §§7.12–7.13, SHA-256
  `3cb18a48cde43c0df94f8e52522cf7fe0a56cdd15b463dea1009cedf8794147c`.
  [Simple statements](https://docs.python.org/release/3.7.17/reference/simple_stmts.html#the-global-statement)
- Python 3.7.17, §3.3.3.6, SHA-256
  `e67c556ea43d2660d174ccaa64e122483170da92dc84512b0837fd163c01dd0b`.
  [Creating the class object](https://docs.python.org/release/3.7.17/reference/datamodel.html#creating-the-class-object)
- Python 3.7.17, §6.14, SHA-256
  `53021dbaf574df1726e3eb15dba1915b8dd7c2c4e06a26bf1782bddd13cb15bd`.
  [Lambdas](https://docs.python.org/release/3.7.17/reference/expressions.html#lambdas)
- Python 3.7.17, §6.2.9, SHA-256
  `53021dbaf574df1726e3eb15dba1915b8dd7c2c4e06a26bf1782bddd13cb15bd`.
  [Yield expressions](https://docs.python.org/release/3.7.17/reference/expressions.html#yield-expressions)
- Python 3.13.5, SHA-256
  `6dba22a6c0f7b3eaf4d413343554182c27653b7d6e134b9a6c36f6ff711b2d4b`.
  [CPython AST and feature version](https://docs.python.org/release/3.13.5/library/ast.html#ast.parse)
- Köhl reference analyzer at `b7ff99372dd24845cf84e58c96b877f15764b276`,
  SHA-256 `88b62abbf9e56479b40299cdc6c1f576d44c8465607439d1391e0cd522d2a139`.
  [Reference scope analyzer](https://github.com/koehlma/rigorous/blob/b7ff99372dd24845cf84e58c96b877f15764b276/rigorous/semantics/python/syntax/blocks.py)
