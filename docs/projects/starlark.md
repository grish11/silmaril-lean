# Scalar Starlark semantics

The collections API adds a shared heap for lists, tuples and dictionaries,
with reachable freezing and function-body iteration.
[Starlark collection store](starlark-lists.md) · [Lexical calls](starlark-functions.md) · [Lean expression quotation](starlark-functions.md#quoting-an-expression-in-lean) · [Built-ins](starlark-builtins.md) · [Modules](starlark-modules.md)

The dialect is the **Starlark core language** specified by the Bazel team in the
[Starlark Language Specification][spec] at commit
`c0af0ea03dc90d3bbc021394b693e6957cc15030` (2026-02-06). The SHA-256 of the raw
`spec.md` is `9e1e2b52717512968270bc99ca79aa8c9014df99a9befd0b47eed59c7c848597`.
The profile uses the core rules for single-assignment globals, function-only
`if`, and arbitrary-precision integers. Application-provided names and
implementation-specific options are outside this profile. The main references
for the slice are [Integers][integers], [Name binding and variables][names],
[Expressions][expressions], [Statements][statements] and
[Module execution][modules].

## Lean entry points

- [Defs](../../Silmaril/Languages/Starlark/Defs.lean) defines the AST,
  values, lexical bindings, frames, control results and scalar primitives.
  `Expr` and `Stmt` are parameterized over reference and assignment names.
  `SourceStmt` uses identifiers and `ResolvedStmt` uses classified lexical
  bindings. Clients supply a normalized AST with valid identifier spellings.
- [Resolution](../../Silmaril/Languages/Starlark/Resolve/Defs.lean) collects
  assignments across a whole lexical block and resolves reads before execution,
  including reads in untaken branches. Locals shadow globals, which can shadow
  the predeclared names `None`, `True` and `False`. A declared slot can be
  uninitialized at run time. A name outside the declared scalar environment
  is rejected at resolution.
- [Denotation](../../Silmaril/Languages/Starlark/Denotation/Defs.lean) composes
  expression meanings `Frame → Result Value` and suite meanings
  `Frame → Result Completion`. `runModule` starts with empty globals and returns
  a global lookup on success. `runFunctionBody` enters a single function body
  with supplied scalar globals and already bound parameters and returns its
  value, defaulting to `None` for a bare return or fallthrough. The caller
  supplies the function context. Function declarations and calls are absent
  from the AST.
- [Operational rules](../../Silmaril/Languages/Starlark/Operational/Defs.lean)
  define `Eval` and `Exec` without calling the denotation. They share the scalar
  operations and frame reads and writes. The rules determine evaluation order,
  branch selection, short-circuiting, early return and first-error propagation.
  [Thms](../../Silmaril/Languages/Starlark/Thms.lean) proves that the two readings
  agree in both directions, for every resolved AST and input frame, including
  dynamic failures. The theorems concern the resolved semantics. Conformance
  of resolution and scalar primitives to the prose specification is checked by
  examples.

The supported values are `None`, Booleans and exact integers. Expressions
include integer literals, reads, unary `+`, unary `-`, `not`, integer
`+`, `-`, `*`, `//`, `%`, scalar comparisons, operand-valued `and` and `or`,
and conditional expressions. Mixed Boolean/integer order comparisons and
arithmetic fail. Integer `//` and `%` use Lean's floored operations after
checking for a zero divisor. Statements include `pass`, expression statements,
single-name assignment, sequencing, and function-body conditionals and
returns. The source entry points observe static rejection separately from a
dynamic error. Dynamic errors carry a category and, where relevant, the
operator or uninitialized binding.

Build the theorem header and the kernel-checked regressions with the pinned
repository toolchain.

```sh
lake build --wfail +Silmaril.Languages.Starlark.Checks
```

[Regression cases](../../Silmaril/Languages/Starlark/Checks.lean) include
large arithmetic, signed floor division and remainder, lazy control, local
reassignment, reads before assignment, and precedence of errors.

## Coverage obligations

C3 remains open while these pinned-spec obligations remain.

| Area | Remaining work under the pinned spec |
| --- | --- |
| Source and validation | UTF-8 lexer, indentation, literal spelling and escapes, grammar and precedence, source locations and diagnostics. A future shared syntax may admit a larger Python surface, with language-specific validation and name resolution. |
| Values and expressions | Floats and mixed numeric coercion/comparisons, further string operations, bytes, sets and general method calls. Add `/`, bitwise operators and shift errors, sequence concatenation and repetition, string interpolation, membership, byte indexing, general comprehension expression positions, attribute access, byte slices, range comparison and formatting, and lambdas. [Collection displays and subscript reads](starlark-functions.md#collection-displays-and-subscript-reads), [lazy range subscripts](starlark-functions.md#lazy-range-subscript-reads) and [slices](starlark-functions.md#lazy-range-slice-reads), [list and tuple slices](starlark-functions.md#list-and-tuple-slice-reads), and [valid UTF-8 string subscripts](starlark-functions.md#string-subscript-reads) and [slices](starlark-functions.md#string-slice-reads) admit calls in their operands. |
| Statements and names | [Standalone destructuring](starlark-functions.md#standalone-pattern-assignment) covers nested name leaves in functions and modules. The comprehension RHS profile also admits [mixed name and subscript targets](starlark-functions.md#mixed-name-and-subscript-targets) with ordinary leaf operands. Field writes, store leaves in loop and comprehension targets, broader leaf operands, augmented operators beyond integer `+=`, module-level name augmentation, and lambdas remain open. [Checked comprehension positions](starlark-functions.md#comprehensions-in-checked-expression-positions) include call, conditional and short-circuit operands, collection displays, index and slice reads, and comprehension clauses and heads. [Simple stores](starlark-functions.md#comprehension-operands-in-simple-subscript-stores) and [integer augmented stores](starlark-functions.md#comprehension-operands-in-integer-augmentation) admit comprehensions in all three operands. Function-local integer `+=` also admits a comprehension-bearing RHS. |
| Iteration | [Normalized source loops](starlark-modules.md#resolving-module-declarations) collect every name in [nested tuple/list targets](starlark-functions.md#loop-target-patterns) into the function block and reuse the resolved cursor over lists, tuples, dictionaries and lazy ranges. The `list` and `tuple` constructors [materialize ranges](starlark-builtins.md#materializing-ranges), and [positional spreading](starlark-functions.md#argument-binding) reads the same range cursor. Iterable types such as string and byte element views remain open. |
| Function defaults | The [source adapter](starlark-modules.md#resolving-module-declarations) resolves defaults in the defining scope. [Comprehensions in defaults](starlark-functions.md#comprehensions-in-parameter-defaults) use the normalized placement grammar and the existing definition-time order and closure storage. Quotation for comprehensions, slot reuse to match Go, and the outstanding expression forms and text-level parameter syntax checks remain open. |
| Module expressions and source | [Native module commands](starlark-modules.md) have exact agreement before publication and across initialization and finite loading. The normalized source adapter validates and resolves name and pattern assignments, the supported subscript updates, expression statements, definitions and load aliases. Independent mixed assignment elaboration is proved for bounded leaf operands and a plain or single-generator list RHS. [Independent block collection](starlark-modules.md#lexical-block-collection) supplies the scope for load-free modules and function bodies in its stated subset. [Independent capture selection and slot installation](starlark-modules.md#nested-function-captures) cover a bounded mixed assignment and return through a finite chain of enclosing functions that define and return their child. [Checked module entry and positional binding](starlark-modules.md#checked-module-entry-and-positional-binding) derive live cells and root capture addresses, prove exact required positional dispatch, and prove the defined error for a first-command read of an uninitialized global. [Root definition sites and ordered positional operands](starlark-modules.md#root-definition-sites-and-call-operands) link actual command positions to declaration IDs, preserve live callees through unrelated bindings, and compose with checked activation for read-only operands. [Wrapper returns and reached prefixes](starlark-modules.md#wrapper-returns-and-reached-command-prefixes) derive exact wrapper-body execution and escaped closures and compose checked command steps through the existing module boundary. [Mixed leaf execution and publication](starlark-modules.md#mixed-leaf-execution-and-publication) compose an independent reached trace for the bounded load-free module profile through the exact exported bindings and frozen heap or a reached error with retained effects. [Trace construction](starlark-modules.md#constructing-the-bounded-module-trace) derives the independent reached trace from checked syntax for one leading definition, a finite linear chain of escaped calls, interleaved setup and the mixed leaf. [Multiple live callees](starlark-modules.md#traces-with-multiple-live-callees) generalize the schedule to interleaved definitions, explicit closure aliases, and independent or repeated calls. [Checked positional defaults](starlark-modules.md#checked-positional-defaults) cover definition-time evaluation and publication for a bounded module definition, and exact later positional preparation at the saved closure cell. [Defaulted calls in the multiple-callee trace](starlark-modules.md#defaulted-calls-in-the-multiple-callee-trace) derive call and return for parameter-return bodies, preserving saved addresses through aliases and interactions with existing wrapper and mixed-leaf calls. [Escaping nested defaults](starlark-modules.md#escaping-nested-defaults) cover a one-parameter wrapper that defines, rebinds and returns its parameter-returning child. [Compositional defaulted bodies](starlark-modules.md#compositional-bodies-for-defaulted-calls) cover sequences of local assignments and returns, deriving module capture addresses at checked entry. [Enclosing captures in defaulted bodies](starlark-modules.md#enclosing-captures-in-defaulted-bodies) link the same body theorem to an escaped child with ordered parameter and local captures. A checked wrapper prefix reads local names and live module cells, supplies the reached heap for default evaluation and capture installation, and preserves exact failure state before the child definition. [Lexical defaults and reached definitions](starlark-modules.md#lexical-defaults-and-reached-definitions) reuse the body operand judgment for ordered definition-time evaluation, including direct module reads, and install the actual defining frame's capture addresses. [Reached nested definitions](starlark-modules.md#reached-nested-definitions-and-forwarded-cells) link a bounded child body to its emitted declaration and derive owned and forwarded capture addresses from the actual parent frame. [Sequencing reached definitions](starlark-modules.md#sequencing-reached-definitions) composes local definitions with intervening assignments and returns in an active frame, preserves IDs through later declarations, and exposes saved defaults for positional call preparation at the same live closure address. [Recursive elaboration of nested suites](starlark-modules.md#recursive-elaboration-of-nested-suites) proves owned and free-reference order, stable declaration indices, and capture address preservation at any finite depth. [Whole-suite execution after activation](starlark-modules.md#whole-suite-execution-after-activation) proves exact return or error for recursive suites and derives an immediate aliased callee operand from an installed closure. [Positional calls through a local closure](starlark-modules.md#positional-calls-through-a-local-closure) connect an installed alias and ordered operands to saved-default binding and the exact checked activation result. [Positional call assignments in recursive suites](starlark-modules.md#positional-call-assignments-in-recursive-suites) compose immediate alias calls through finite chains of call-bearing children by induction on the reduced available declaration set. The result is committed in the restored caller frame. [Live local closure provenance](starlark-modules.md#live-local-closure-provenance) admits transitive copies across intervening statements and resolves rebound callees from their reached slots and closure records. [Explicit named arguments](starlark-modules.md#explicit-named-arguments-at-tracked-local-calls) prove independent binder agreement on ordered delivery and failure. [Bare-star keyword-only parameters](starlark-modules.md#keyword-only-parameters-in-checked-local-suites) extend checked nested definitions and tracked calls to required and defaulted keyword-only formals, preserving definition-time default order and the positional limit. [Named positional collection](starlark-modules.md#named-positional-collection-in-checked-local-suites) binds surplus positional values to the exact tuple after successful binding and retains that allocation on a reached body error. [Terminal keyword collection](starlark-modules.md#terminal-keyword-collection-in-checked-local-suites) binds the ordered unmatched explicit names and original values to a fresh dictionary after successful binding, immediately after the positional collector when both exist. [Terminal positional spread](starlark-modules.md#terminal-positional-spread-in-checked-local-suites) extends tracked-local call assignments with checked list and tuple displays, transporting their ordered elements and live references after all operands succeed. [Terminal mapping spread](starlark-modules.md#terminal-mapping-spread-in-checked-local-suites) admits a checked dictionary display after any positional spread. It validates string keys after operand evaluation and before positional expansion, and delivers the ordered original values through the ordinary binder. [Checked source calls through publication](starlark-modules.md#checked-source-calls-through-module-publication) reuse the tracked call proof for a finite load-free module plan with linked recursive suites, defaults, global closure aliases, named arguments and both spreads. Independent sequencing determines exact published exports and freezing or the reached error and retained heap. [Callable returns through publication](starlark-modules.md#callable-returns-through-module-publication) derive an escaped local closure from the reached return value and heap and preserve its linked declaration, captures and saved defaults through module assignments, named and spread calls, and publication. [Checked callable imports](starlark-modules.md#checked-callable-imports) derive the linked record from actual producer publication or cache and consumer import-slot lookup on a two-module acyclic source profile, then preserve callable provenance through finite sequences of checked assignments and calls. General carrier expressions, untracked dispatch, consumer declarations, broader cache histories and a general source manifest theorem remain open. |
| Built-in functions | `abs`, `any`, `all`, `bytes`, `dict`, `dir`, `enumerate`, `fail`, `float`, `getattr`, `hasattr`, `hash`, `int`, `max`, `min`, `print`, `repr`, `reversed`, `set`, `sorted`, `str`, `zip`. Extend `bool`, `len`, `list`, `tuple` and `type` as new value types enter the domain. |
| Collection methods | Bytes `elems`. Dict `clear`, `get`, `items`, `keys`, `pop`, `popitem`, `setdefault`, `update`, `values`. List `clear`, `extend`, `index`, `insert`, `pop`, `remove`. Set `add`, `clear`, `difference`, `difference_update`, `discard`, `intersection`, `intersection_update`, `isdisjoint`, `issubset`, `issuperset`, `pop`, `remove`, `symmetric_difference`, `symmetric_difference_update`, `union`, `update`. |
| String methods | `capitalize`, `count`, `elems`, `endswith`, `find`, `format`, `index`, `isalnum`, `isalpha`, `isdigit`, `islower`, `isspace`, `istitle`, `isupper`, `join`, `lower`, `lstrip`, `partition`, `removeprefix`, `removesuffix`, `replace`, `rfind`, `rindex`, `rpartition`, `rsplit`, `rstrip`, `split`, `splitlines`, `startswith`, `strip`, `title`, `upper`. |
| Host and modules | Effectful and concurrent loading beyond the finite manifest, host thread state, host predeclared and pre-bound values, custom types and callable methods, `print` output and failure backtraces. Resource limits, cancellation and enabled extensions belong to explicit profiles. |

See the pinned sections on [value concepts][values], [loading][loading],
[built-in functions][builtins] and [built-in methods][methods].

## Semantic domains for the extended language

Structural recursion suffices for the finite scalar trees. The current
`Except` records a dynamic error distinctly from a successful Starlark
`None`. In a larger semantics, calls and host requests can require a partial
or interactive computation around the terminal result. Core recursion
rejection, finite iteration and any termination proof should state their
assumptions on callable host values and loaders. A bounded executable
interpreter should distinguish budget exhaustion from a language error and
from a semantic claim of divergence. [Imp's partial-state denotation](../../Silmaril/Calculi/Imp/Denotation.lean)
and the [interaction-tree handler interface](../../Silmaril/Semantics/ITreeInterpret/Defs.lean)
are existing models for these choices.

Mutable objects need identities and a store. Binding slots and captured cells
can then refer to the same object, and a closure can retain the lexical cells
and defining module that its body reads. Immutable containers can still reach
mutable objects. Freezing follows the reachable graph with cycle handling and
preserves aliases. It also reaches values captured by exported functions,
including parameter defaults. Iteration needs defined order, iterator lifetime
and active mutation checks for the containers the spec guards. Equality and
hashing must handle sharing, cycles and hashability.

Loading and host calls can be typed requests with explicit responses and a
separate policy for cache identity, allowed effects and host state. Successful
module initialization freezes the shareable values. A failure terminates
execution while preserving prior observations such as output already emitted.
The full result domain needs a way to retain those observations even on failure.

## Shared-syntax agreement

Use one unresolved input AST and perform lexical resolution under each
language's rules. State an admissibility predicate for the common fragment and
relate the two initial environments. Compare tagged scalar values
(`int`, `bool`, `None`), a selected set of final global bindings for modules
or a returned value for functions, and the phase and agreed class of any
failure. Fix a projection for Python exceptions and Starlark errors. Source
locations, diagnostic wording and internal frame identity are outside this
scalar observation. When state and effects enter the common fragment, compare
observable mutations under a correspondence of allocated identities, and
compare the ordered host observations under related handlers. Divergence and
budget exhaustion require distinct observations if the selected profile
admits them.

The common syntax `out = 1 == True` yields `False` in this Starlark profile
and `True` in Python. An agreement theorem therefore needs a restriction on
mixed Boolean/numeric equality or a separate semantic precondition. The
Starlark side is checked in Lean and agrees with the default
[starlark-go CLI at `4f4267fb`][go]. The language references specify the
comparison behavior. [Starlark Booleans][bool], [Python Boolean type][python]

[spec]: https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md
[integers]: https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#integers
[names]: https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#name-binding-and-variables
[expressions]: https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#expressions
[statements]: https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#statements
[modules]: https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#module-execution
[values]: https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#value-concepts
[loading]: https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#load-statements
[builtins]: https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#built-in-constants-and-functions
[methods]: https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#built-in-methods
[bool]: https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#booleans
[python]: https://docs.python.org/3.14/library/stdtypes.html#boolean-type-bool
[go]: https://github.com/google/starlark-go/tree/4f4267fb140d1e8b91c9bce55cee2f809e8840dd
