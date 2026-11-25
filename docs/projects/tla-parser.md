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
including `..`, `...`, `:=`, `::=`, `[]ASSUME`, `]_` and `>>_`.
It recognizes reserved words after scanning identifiers and gives `WF_` and
`SF_` their dedicated token boundary.

Postfix operators, indexes and field selections extend an operand in source
order. An index can follow a prime (`f'[i]`) or precede it (`f[i]'`).
A pending operator still participates in the precedence check, so `[]x'`
requires parentheses. `f[i,j]`, `f[<<i,j>>]` and `F(i,j)` produce different
trees. Action and fairness subscripts use the `ReducedExpression` grammar.
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

## Grammar coverage

Statuses describe the named Surface path. **Landed** refers to the existing
AST and codec. **Implemented** refers to this parser. **Remaining** identifies
productions for follow-up work and **Unsupported** identifies deliberate
boundary cases that require a representation or source contract decision.

| Status | Pinned SANY productions | Coverage |
| --- | --- | --- |
| Landed | Surface inventory and codec | Module, expression and proof trees from [#2513](https://github.com/hiloopai/silmaril-lean/pull/2513) and the full [version 1 S-expression schema](tla-surface-sexp.md) from [#2544](https://github.com/hiloopai/silmaril-lean/pull/2544). |
| Implemented | `CompilationUnit`, `Module`, `BeginModule`, `EndModule`, `Extends`, `Body` | A complete header, optional EXTENDS, ordered units and nested modules, separators and a required terminator. |
| Implemented | `Identifier`, `Number`, `String` and lexical states | ASCII identifier rules, number-set aliases, decimal and base-prefixed naturals, decimal fractions, string escapes, reserved words, longest operators, line comments and nested block comments. |
| Implemented | `VariableDeclaration`, `ParamDeclaration`, `Recursive`, `IdentDecl`, `SomeFixDecl` | Variable and constant groups, named arities and symbolic declarations. |
| Implemented | `OperatorOrFunctionDefinition`, `IdentLHS`, `PrefixLHS`, `InfixLHS`, `PostfixLHS`, `Instance`, `Instantiation`, `Substitution`, `LetIn`, `LetDefinitions` | Operator and bounded function definitions, LOCAL, named and anonymous instances, WITH substitutions, LET and RECURSIVE. |
| Implemented | `Expression`, `ExtendableExpr`, `OpenExpression`, `ParenExpr`, operator token productions | Precedence ranges, canonical operator identity, mixfix minus, fixed-arity operators, Cartesian chains, grouping and ordinary identifier labels with optional identifier parameters. |
| Implemented | `PrimitiveExp`, `OpArgs`, `OpSuite`, `OpOrExpr`, `Lambda`, `BangExt`, `StructOp` | Named and symbolic references, applications, qualified references and structural selectors, bare operator arguments and lambdas. |
| Implemented | `SomeQuant`, `SomeTQuant`, `QuantBound`, `IdentifierTuple`, `UnboundOrBoundChoose`, `MaybeBound` | Rigid and temporal binders, tuple and shared-domain patterns, CHOOSE. |
| Implemented | `BraceCases`, `SBracketCases`, `TupleOrAction`, `FieldVal`, `FieldSet`, `ExceptSpec`, `ExceptComponent` | Sets, bounded functions and function sets, records and record sets, tuples, indexing, selection and EXCEPT paths with old-value expressions. |
| Implemented | `ReducedExpression`, `NoOpExtension`, `FairnessExpr` and action alternatives | Square and angle action brackets with one body, WF and SF. Restricted subscripts admit named reference chains and delimited expressions. |
| Implemented | `IfThenElse`, `Case`, `CaseArm`, `OtherArm`, `Junctions`, `DisjList`, `ConjList`, `JuncItem` | IF, CASE including final OTHER, and aligned junction lists including Unicode markers. |
| Implemented | `Assumption`, `Theorem`, `AssumeProve`, `NewSymb` | Named or unnamed assumptions and theorems, nested and labeled ASSUME/PROVE hypotheses, boxed modes and NEW hypotheses. |
| Implemented | terminal `Proof`, `UseOrHideOrBy` | Omitted proof, OMITTED, OBVIOUS, BY with facts and DEF lists, and module-level USE/HIDE. Module-level USE ONLY is a SANY syntax rejection. |
| Remaining | hierarchical `Proof`, `StepStartToken`, `Step`, `QEDStep` | Explicit and relative proof levels, step labels, nested proofs and QED with its optional proof. |
| Remaining | `DefStep`, `HaveStep`, `TakeStep`, `WitnessStep`, `PickStep`, `CaseStep`, `AssertStep` and step alternatives | DEFINE and unmarked definitions, HAVE, TAKE, WITNESS, PICK, CASE, assertions, SUFFICES, INSTANCE, USE and HIDE within step proofs. |
| Remaining | proof-step alternatives of `PrimitiveExp` | Numbered and current-level step references, including references in citations and as qualified heads. |
| Unsupported | `Prelude` and JavaCC default-mode text | Leading arbitrary prose and the `--->` pragma. The native API also rejects trailing text or another top-level module after the terminator. |
| Unsupported | permissive label alternative of `ExtendableExpr` | Nonidentifier labels or arguments accepted by JavaCC lookahead. The Surface label stores a name and identifier parameters. |
| Unsupported | permissive `TupleOrAction` alternatives | Angle-action forms with zero or multiple apparent bodies. The Surface action stores one body. |
| Unsupported | Bare index payload in `ParenthesesExpression` or `ReducedExpression` | SANY can recognize `[x]` as a function-application payload without a function. The Surface index requires a function expression. |
| Unsupported | permissive `Number` alternative | A decimal with a base-prefixed whole or fractional token. The Surface decimal stores an exact base-ten fraction. |
| Unsupported | outside the TLA+ module grammar | TLC configuration and PlusCal translation. A PlusCal algorithm inside a TLA+ block comment is consumed as comment text. |

Proof steps and step references are the first follow-up because their
constructors already exist in the Surface tree. Next, extend the differential
corpus around overlapping grammar alternatives and settle input compatibility
with SANY's prelude and permissive syntax. Elaboration is a separate downstream
task.

## Validation and provenance

Run from the repository root. The default check uses the native parser and
local fixtures. `--upstream` also downloads the three original example modules.
`--sany` additionally requires a JDK and Ant, runs the vendored JavaCC
generator, builds SANY from the pinned upstream source, and calls `TLAplusParser.parse()` directly. This
returns a syntax verdict without invoking SANY's semantic frontend, which
would load EXTENDS modules and resolve names and operators. The case table
records deliberate policy differences, including trailing text after a
compilation unit, which the SANY entry point can leave unread.

~~~sh
python3 -I tests/semantics/tla-parser/check.py
python3 -I tests/semantics/tla-parser/check.py --sany
make check CHECK_TARGETS='+Silmaril.Logic.Temporal.TLA.Surface.Parser.Defs'
~~~

The fixture check verifies downloaded bytes by SHA-256 and uses intact
HourClock, LiveHourClock and DieHard from the TLA+ tree at
`bc1b506bdcad80bb518bf3776a9161c34ff0fc4c`. It reads BoundedCounter and
BitPair in place and checks their hashes against the original export tree at
`6606bd00bde1c71430aa254ce78a716dd6d59267`. Native tests assert tree shapes
and diagnostic positions in addition to whole-source verdicts.
[Fixture driver and hashes](../../tests/semantics/tla-parser/check.py) ·
[Verdict cases](../../tests/semantics/tla-parser/cases.json) ·
[Pinned Quint export tree](https://github.com/hiloopai/silmaril-lean/tree/6606bd00bde1c71430aa254ce78a716dd6d59267/tests/semantics/tla-quint)

The SHA-256 of the pinned `tla+.jj` is
`bfc981f31c205333f478b773ab108159b5e2d339b659d33b0f920d56ebf4253d`.
The SHA-256 of `Operators.java` is
`92a6ce59163441b2ab607cddcd5cd9cdb6aefe8c42de6582acaff2365bba2b47`.
The reducer also uses the comparison and shift rules in `Operator.java` and
`OperatorStack.java`. [JavaCC grammar](https://github.com/tlaplus/tlaplus/blob/bc1b506bdcad80bb518bf3776a9161c34ff0fc4c/tlatools/org.lamport.tlatools/javacc/tla%2B.jj) ·
[Operator table](https://github.com/tlaplus/tlaplus/blob/bc1b506bdcad80bb518bf3776a9161c34ff0fc4c/tlatools/org.lamport.tlatools/src/tla2sany/parser/Operators.java) ·
[Operator stack](https://github.com/tlaplus/tlaplus/blob/bc1b506bdcad80bb518bf3776a9161c34ff0fc4c/tlatools/org.lamport.tlatools/src/tla2sany/parser/OperatorStack.java)
