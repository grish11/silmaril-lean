# Native TLA+ source parser

Import [the parser header](../../Silmaril/Logic/Temporal/TLA/Surface/Parser/Defs.lean)
and use the namespace `Silmaril.Logic.Temporal.TLA.Surface.Parser`.

~~~lean
parseModule (source : String) : Except Diagnostic Module
parseExpr   (source : String) : Except Diagnostic Expr
~~~

`parseModule` consumes one complete compilation unit, including its header and
terminator. `parseExpr` consumes one complete expression using the same grammar
and operator and indentation rules. Both accept surrounding whitespace and
comments. Each failure returns one diagnostic with a half-open UTF-8 byte
span, one-based line and column, and a lexical, syntax, precedence or
unsupported classification. CRLF counts as one newline, tabs advance to
eight-column stops, and other characters count as one column. The lexer scans
the source before the grammar checks it. The span is empty at end of input.

The native entry point uses Lean and its standard library. The trees keep names
and symbolic operators for downstream resolution. For example, `x' := e`
produces an `Expr.infix (.symbol ":=")` with a primed left operand. Pinned SANY
parses `:=` as an ordinary infix operator at precedence 5. The Apalache
module supplies its definition.

## Operator and layout rules

The operator table follows SANY's precedence intervals and aliases. An operator
binds more tightly when its entire interval lies above the other operator's
interval. A pending operator and an incoming infix or postfix operator with
overlapping intervals require parentheses unless they belong to the same
left-associative operator, including synonyms. The tree preserves ordinary
symbol spellings. Parentheses start a fresh precedence context and preserve
grouping in nested Cartesian products. The lexer matches the longest token,
including `..`, `...`, `@@`, `:=`, `::=`, `[]ASSUME`, `]_` and `>>_`.
It recognizes reserved words after scanning identifiers and gives `WF_` and
`SF_` their dedicated token boundary. A single `@` keeps its old-value
or structural-selector meaning. `@@` is an infix operator and can also
appear as a symbolic operator argument or selector.

Postfix operators, indexes and field selections extend an operand in source
order. An index can follow a prime (`f'[i]`) or precede it (`f[i]'`).
A pending operator still participates in the precedence check, so `[]x'`
requires parentheses. `f[i,j]`, `f[<<i,j>>]` and `F(i,j)` produce different
trees. For a label under a pending operator, the precedence check treats
`L:: (b + c)` as a grouped body and `L:: (b) + c` as a body rooted at `+`.
Action and fairness subscripts use the `ReducedExpression` grammar.
For example, `[A]_f[i]` indexes the action expression. `[A]_(f[i])` places the
index inside the subscript.

`/\` and `\/` and their Unicode spellings start a junction list when an
operand is expected. A marker of the same kind in the same column starts a
sibling. A marker to its right can start a nested list in operand position or
act as a binary operator after an operand. A different marker in the same
column, or a dedented marker, ends the list and may serve as an outer infix
operator. Parenthesizing an item preserves the enclosing indentation rule.
These rules follow SANY's `JunctionListContext` and *Specifying Systems*
§§15.2.1–15.2.2. [Book](https://lamport.azurewebsites.net/tla/book-21-07-04.pdf)

## Proof hierarchy and reference syntax

SANY uses the first step header to set a proof's level. A proof starting with
`<*>` or `<+>` has level zero at the theorem and one more than its parent
inside a proof. A numeric child level can skip numbers, provided it exceeds
the parent's level. Siblings and the closing QED share the proof's level.
Within a proof, `<*>` continues that level unless `PROOF` opens a child proof.
`<+>` opens a child proof where the grammar permits one. The header level
determines nesting independently of indentation. Each hierarchical proof ends
with a QED and its own step header, even with zero preceding steps. The QED
can itself have a terminal or hierarchical proof. The parser follows SANY's
100-proof nesting limit and uses arbitrary-precision levels where SANY uses
signed Java integers for headers.

Surface preserves the spelling of each step name and the choice of numeric,
`<*>` or `<+>` level. Numerals in headers and references become `Nat` values,
so leading zeros disappear from the level. `PROOF`, `DEFINE`, the `-|-`
definition marker, trailing header dots, and the nameless header suffixes `*`
and `-` carry no field in the tree. Name underscores are accepted in numeric
and dotted headers, following the pinned lexer.

Within a hierarchical proof, named undotted `<n>name` and `<*>name` tokens
can head expressions and citations, including qualified forms such as
`<1>a!Label(2)!1`. A leaf proof within a hierarchy inherits the enclosing
context. A theorem statement, a standalone `parseExpr` call and a theorem's
top-level terminal proof have no such context. `<+>name` is header syntax.
After an empty `BY`, `USE` or `HIDE`, a named undotted token can be consumed
as the first citation. A dotted or nameless header avoids that ambiguity.
A nested module header ends an empty citation list. The standalone
`MODULE` keyword can still introduce a module citation.

The parser checks levels and where child proofs may appear. Step name
uniqueness, whether a reference denotes an available step or selector, what
may appear in a citation, and proof obligations belong to later passes.
The `CASE` step consumes a condition expression. Use parentheses to make
an assertion whose expression begins with `CASE … -> …`.
[Pinned SANY grammar](https://github.com/tlaplus/tlaplus/blob/bc1b506bdcad80bb518bf3776a9161c34ff0fc4c/tlatools/org.lamport.tlatools/javacc/tla%2B.jj)

## Grammar coverage

Statuses describe the named Surface path. **Landed** refers to the existing
AST and codec. **Implemented** refers to this parser. **Unsupported** identifies
forms outside the Surface representation or the complete-input contract.

| Status | Pinned SANY productions | Coverage |
| --- | --- | --- |
| Landed | Surface inventory and codec | Module, expression and proof trees from [#2513](https://github.com/hiloopai/silmaril-lean/pull/2513) and the full [version 1 S-expression schema](tla-surface-sexp.md) from [#2544](https://github.com/hiloopai/silmaril-lean/pull/2544). |
| Implemented | `CompilationUnit`, `Module`, `BeginModule`, `EndModule`, `Extends`, `Body` | A complete header, optional EXTENDS, ordered units and nested modules, separators and a required terminator. |
| Implemented | `Identifier`, `Number`, `String` and lexical states | ASCII identifier rules, number-set aliases, decimal and base-prefixed naturals, decimal fractions, string escapes, reserved words, longest operators including `@@`, line comments and nested block comments. |
| Implemented | `VariableDeclaration`, `ParamDeclaration`, `Recursive`, `IdentDecl`, `SomeFixDecl` | Variable and constant groups, named arities and symbolic declarations. |
| Implemented | `OperatorOrFunctionDefinition`, `IdentLHS`, `PrefixLHS`, `InfixLHS`, `PostfixLHS`, `Instance`, `Instantiation`, `Substitution`, `LetIn`, `LetDefinitions` | Operator and bounded function definitions, LOCAL, named and anonymous instances, WITH substitutions, LET and RECURSIVE. |
| Implemented | `Expression`, `ExtendableExpr`, `OpenExpression`, `ParenExpr`, operator token productions | Precedence ranges, canonical operator identity, mixfix minus, fixed-arity operators, Cartesian chains, grouping and ordinary identifier labels with optional identifier parameters. |
| Implemented | `PrimitiveExp`, `OpArgs`, `OpSuite`, `OpOrExpr`, `Lambda`, `BangExt`, `StructOp` | Named and symbolic references, applications, qualified references and structural selectors, bare operator arguments and lambdas. The bare operator-argument alternative accepts `×` and rejects `\X` and `\times`. |
| Implemented | `SomeQuant`, `SomeTQuant`, `QuantBound`, `IdentifierTuple`, `UnboundOrBoundChoose`, `MaybeBound` | Rigid and temporal binders, tuple and shared-domain patterns, CHOOSE. |
| Implemented | `BraceCases`, `SBracketCases`, `TupleOrAction`, `FieldVal`, `FieldSet`, `ExceptSpec`, `ExceptComponent` | Sets, bounded functions and function sets, records and record sets, tuples, indexing, selection and EXCEPT paths with old-value expressions. |
| Implemented | `ReducedExpression`, `NoOpExtension`, `FairnessExpr` and action alternatives | Square and angle action brackets with one body, WF and SF. Restricted subscripts admit named reference chains and delimited expressions. |
| Implemented | `IfThenElse`, `Case`, `CaseArm`, `OtherArm`, `Junctions`, `DisjList`, `ConjList`, `JuncItem` | IF, CASE including final OTHER, and aligned junction lists including Unicode markers. |
| Implemented | `Assumption`, `Theorem`, `AssumeProve`, `NewSymb` | Named or unnamed assumptions and theorems, the optional `-|-` marker before an assumption name, nested and labeled ASSUME/PROVE hypotheses, boxed modes and NEW hypotheses. |
| Implemented | terminal `Proof`, `UseOrHideOrBy` | Omitted proof, OMITTED, OBVIOUS, BY with facts and DEF lists, and module-level USE/HIDE. A submodule header ends citation lookahead. Module-level USE ONLY is a SANY syntax rejection. |
| Implemented | hierarchical `Proof`, `StepStartToken`, `Step`, `QEDStep` | Explicit and relative proof levels, optional names and punctuation, nested proofs and QED with its optional proof. |
| Implemented | `DefStep`, `HaveStep`, `TakeStep`, `WitnessStep`, `PickStep`, `CaseStep`, `AssertStep` and step alternatives | DEFINE and unmarked definitions, HAVE, TAKE, WITNESS, PICK, CASE, assertions, SUFFICES, INSTANCE, USE and HIDE within step proofs. |
| Implemented | proof-step alternatives of `PrimitiveExp` | Numbered and current-level step references in expressions, including citations and qualified heads. |
| Unsupported | `Prelude` and JavaCC default-mode text | Leading arbitrary prose and the `--->` pragma. The native API also rejects trailing text or another top-level module after the terminator. |
| Unsupported | permissive label alternative of `ExtendableExpr` | Nonidentifier labels or arguments accepted by JavaCC lookahead. SANY accepts `<1>other :: TRUE` and `L(<1>other) :: TRUE` in a proof. Both receive `unsupported` diagnostics because `Surface.Label` stores identifier names and parameters. |
| Unsupported | permissive `TupleOrAction` alternatives | Angle-action forms with zero or multiple apparent bodies. The Surface action stores one body. |
| Unsupported | Bare index payload in `ParenthesesExpression` or `ReducedExpression` | SANY can recognize `[x]` as a function-application payload without a function. The Surface index requires a function expression. |
| Unsupported | `FairnessExpr` via `OpOrExpr` | SANY accepts `WF_f(LAMBDA x: x)`. Surface represents lambdas as operator arguments and the fairness action field requires an expression. |
| Unsupported | permissive `Number` alternative | A decimal with a base-prefixed whole or fractional token. The Surface decimal stores an exact base-ten fraction. |
| Unsupported | outside the TLA+ module grammar | TLC configuration and PlusCal translation. A PlusCal algorithm inside a TLA+ block comment is consumed as comment text. |

### Remaining observed grammar differences

| Pinned SANY behavior | Native behavior |
| --- | --- |
| `a * L:: b + c ^ d` passes the label check because SANY uses the last parsed operator `^`. | The check uses the root operator `+` and rejects the ungrouped body. |
| `WF_[A]_f(B)` borrows `(B)` from the nested reduced subscript and uses `B` as the fairness action. | The parser consumes `f(B)` as a subscript reference and requires an explicit fairness action. |
| In `INSTANCE M WITH F <- A!~` followed by `x == TRUE`, SANY inserts a definition boundary before `~` and rejects the selector. | The parser accepts the qualified prefix selector and the following definition. |
| A numeric header level of `2147483648` overflows SANY's signed integer conversion. | Header levels use arbitrary-precision naturals. |

The complete-input contract rejects arbitrary text before or after the
compilation unit and rejects a second top-level module. The verdict fixtures
exercise these cases, the pragma, and the first three grammar differences
in the table.

## Validation and provenance

Run from the repository root. The default check uses the native parser and
local fixtures. `--upstream` also downloads the pinned example and proof modules.
`--sany` additionally requires a JDK and Ant, runs the vendored JavaCC
generator, builds SANY from the pinned upstream source, and calls `TLAplusParser.parse()` directly. This
returns a syntax verdict without invoking SANY's semantic frontend, which
would load EXTENDS modules and resolve names and operators. The case table
records deliberate policy differences, including trailing text after a
compilation unit, which the SANY entry point can leave unread.

~~~sh
python3 -I tests/semantics/tla-parser/check.py
python3 -I tests/semantics/tla-parser/check.py --sany
make check CHECK_TARGETS='+Silmaril.Logic.Temporal.TLA.Surface.Parser.Grammar +Silmaril.Logic.Temporal.TLA.Surface.Parser.Lexer'
~~~

The fixture check verifies downloaded bytes by SHA-256. It uses intact
HourClock, LiveHourClock, DieHard, TLC, WriteThroughCache, ABCorrectness,
the TLAPS `VoteProof` specimen, and SANY's `AssumeProveTest`,
`ImplicitProofsTest`, `ProofsTest` and `StepExpressionsTest` from the
pinned TLA+ tree. It reads
BoundedCounter and BitPair in place and checks their hashes against the
original export tree at `6606bd00bde1c71430aa254ce78a716dd6d59267`. Native
tests compare the full encoded trees of `BoundedQueue`, `ProofSteps` and
`Compatibility` against handwritten Surface trees, and check diagnostic positions and
whole-source verdicts. `make check` runs the native regression whenever a
scoped target is in the parser namespace.
[Fixture driver and hashes](../../tests/semantics/tla-parser/check.py) ·
[Verdict cases](../../tests/semantics/tla-parser/cases.json) ·
[Pinned VoteProof](https://github.com/tlaplus/tlaplus/blob/bc1b506bdcad80bb518bf3776a9161c34ff0fc4c/tlatools/org.lamport.tlatools/test-model/VoteProof/VoteProof.tla) ·
[Pinned Quint export tree](https://github.com/hiloopai/silmaril-lean/tree/6606bd00bde1c71430aa254ce78a716dd6d59267/tests/semantics/tla-quint)

The SHA-256 of the pinned `tla+.jj` is
`bfc981f31c205333f478b773ab108159b5e2d339b659d33b0f920d56ebf4253d`.
The SHA-256 of `Operators.java` is
`92a6ce59163441b2ab607cddcd5cd9cdb6aefe8c42de6582acaff2365bba2b47`.
The reducer also uses the comparison and shift rules in `Operator.java` and
`OperatorStack.java`. [JavaCC grammar](https://github.com/tlaplus/tlaplus/blob/bc1b506bdcad80bb518bf3776a9161c34ff0fc4c/tlatools/org.lamport.tlatools/javacc/tla%2B.jj) ·
[Operator table](https://github.com/tlaplus/tlaplus/blob/bc1b506bdcad80bb518bf3776a9161c34ff0fc4c/tlatools/org.lamport.tlatools/src/tla2sany/parser/Operators.java) ·
[Operator stack](https://github.com/tlaplus/tlaplus/blob/bc1b506bdcad80bb518bf3776a9161c34ff0fc4c/tlatools/org.lamport.tlatools/src/tla2sany/parser/OperatorStack.java)
