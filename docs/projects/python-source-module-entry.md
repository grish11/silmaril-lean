# Python module-entry source profile

The source checker reads the actual module scope analysis and retains a
typed global reference for each read and write. Readers and assignment
targets carry their name and exact access, including an explicit
`global` declaration. An uninitialized name read still carries its key so
the runtime can give the defined lookup outcome.

The plan contains single-name assignments and assertions in source order.
Operands include signed integers, booleans, global reads, addition, floor
division and a single equality comparison. Bare `global` and `pass`
provide the corresponding scope and statement evidence. The plan supplies
operations to the module runtime, which gives the initialized store and
execution outcomes.
[Definitions and translation laws](../../Silmaril/Languages/Python/Compile/ModuleEntry/Thms.lean)

A list or tuple of signed integer literals can be indexed by a signed
integer literal. The checker adjusts a negative index once by the
sequence length and lowers a successful lookup to an integer operand.
All elements must be integer literals. Out-of-bounds indices, slices,
and dynamic receivers or indices are outside the profile.

Module `if` statements admit Boolean and signed integer literal guards.
Both arms must consist of single-name assignments, message-free assertions
and `pass`, with every operand checked by the scalar profile. Scope analysis
visits the entire statement before this check. Declarations, nested scopes,
and other statement forms in either arm prevent elision.

The translation certifies the decoded truth value and both arms, and emits
the selected actions in source order before the remaining module.
Literal Boolean assertions in an arm lower to the equivalent integer truth
tests. Both runners use their existing transitions, preserving writes before
a failing assertion or lookup and skipping later statements on failure.

Scalar conditional expressions accept the same literal guards. The checker
validates both operands in the analyzed module scope and emits only the
selected operand. A selected Boolean literal uses the existing Boolean
result of equality with `True`. The resulting value retains its Boolean
type in ordinary and seeded execution. Other operands keep their existing
value and failure semantics. The unselected operand performs no lookup.

The scalar checker folds single equality and inequality comparisons over
closed list and tuple expressions. Leaves are flat sequences of exact
Boolean or signed integer literals. A concatenation must join sequences
of the same kind and its certificate retains their element order. Both
sides of the comparison require certificates, including when their
kinds or lengths differ. Equality compares sequence kind, length and
corresponding values, including Boolean and integer equality at zero and
one. Tuple membership keeps the flat literal profile. The result is an
exact Boolean with no runtime sequence value or allocation.

A message-free assertion can compare `len(sequence)` for equality or
inequality against a checked scalar operand. The sequence uses the closed
list or tuple certificate above. Its elements and intermediate objects
have no runtime uses outside the call. The plan retains the checked global
read of `len` and the exact length. The ordinary namespace reports a missing
`len` or an unsupported function receiver, or raises a defined error for
a noncallable scalar. Seeded execution resolves the current module-first
binding and uses the certified length only with the exact stock `len`
descriptor. It records the call result before checking the right operand.
This path uses the existing explicit seed that already supplies `len`.

Run the CPython 3.13.5 controls and the fixed original inputs with
`python3.13 -I scripts/check-python-sequence-length.py --upstream /path/to/pinned/rigorous`.

The same integer-result assertion path accepts `ord` with one positional
text literal containing exactly one Unicode code point. The checker
certifies the code point, including surrogate code points, before lowering.
The independent `legacyOrdSeed` supplies the stock descriptor. The live
module-first lookup precedes comparison against the right operand. A scalar
mask raises the defined noncallable error and a different callable falls
outside the profile. The call receipt records the integer result before a
right-operand failure, and both heaps keep their incoming contents.
Text arguments of other lengths fail the source check. Run the unchanged
`testord.py` and CPython 3.13.5 controls with
`python3.13 -I scripts/check-python-ordinal.py --upstream /path/to/pinned/rigorous`.

The positional argument checker can emit exact literals for closed signed
integer bit operations and single numeric comparisons. The integer profile
accepts unary sign and complement, bitwise AND, OR and XOR, and nonnegative
shifts. Left shift counts up to 4096 bound compile-time growth. Comparisons
accept exact Boolean literals and closed integer operands and retain the
Boolean result tag. Each operand is checked in full before a result is emitted.

Both runners receive the same literal argument and use their existing
call preparation and delivery. Lookup stays live and module-first. A missing
callee stops before reading arguments, while a noncallable binding is tested
after preparing the arguments. Seeded receipts come from the reached call
path and retain the existing error and result tags. Run the unchanged
`bool-compare.py` and `bitwise_test.py` with the CPython 3.13.5 controls using
`python3.13 -I scripts/check-python-numeric-arguments.py --upstream /path/to/pinned/rigorous`.

The function-aware checker can omit an `if` whose closed guard selects an
empty arm or an arm of `pass` statements. The otherwise unsupported arm
must contain only passes or syntactically checked raises. Its exception
names and calls are unreachable. A selected raise or a guard whose
evaluation falls outside the checked profile reports `statementProfile`.
The existing literal-arm lowering handles assignments and assertions.

Closed guards compose integer operations, exact singleton identity,
Boolean selection, and ordered comparisons. Finite float addition and
comparison use the library's binary64 semantics. Text comparison follows
Unicode code-point order, and truth of a literal dictionary requires a
checked text key and literal value at every entry. Boolean selection
retains the selected value's tag. The checker validates every operand and
comparison link, including skipped ones. Bitwise inversion requires an
integer because CPython 3.13.5 warns on Boolean inversion. Emission adds no
instructions, runtime allocations or receipts. Run the four pinned inputs and the
CPython 3.13.5 controls with
`python3.13 -I scripts/check-python-closed-guards.py --upstream /path/to/pinned/rigorous`.

A message-free assertion can use `bool()` or `bool(scalar)` on the left
of a single `is` or `is not` link. The checker certifies the optional
positional operand in the shared scalar profile and the right operand in
the singleton profile. Seeded execution reads the live module-first
`bool` binding before preparing the argument. The existing
`legacyBoolIsinstanceSeed` supplies the exact stock type in both
placements. A noncallable mask fails after argument preparation. The
ordinary runner uses its explicit namespace and the same error order.

The stock descriptor uses scalar truth and returns an exact Boolean.
The receipt records that value before the right operand is evaluated.
The identity test uses the existing singleton rule. A failure retains
the caller bindings and both heaps, and skips the tail. Run the exact
CPython 3.13.5 pin and controls with
`python3.13 -I scripts/check-python-bool-identity.py --upstream /path/to/pinned/rigorous`.

A message-free module assertion can compare a stock `list` construction
with an exact flat list literal on either side of equality. The call
accepts zero arguments or one positional flat list or tuple literal.
The checker preserves the scalar tags and order of all elements, and
requires a module global reference for the constructor. The independent
`legacyListSeed` supplies the stock descriptor in both harness placements.

The seeded runner evaluates the operands in source order. It looks up
`list` before allocating a list argument and tests callability after
preparing that argument. A stock call appends a fresh object to the list
allocation table even when the result is empty or matches a prior list.
The receipt records its address and contents. The comparison uses the
closed sequence equality above. The table records reached allocations,
including temporary lists, and keeps the closure-cell heap separate.
An error retains the reached table and skips the tail. The ordinary
runner has no stock list descriptor and keeps its existing namespace
and cell heap on a missing name or noncallable mask.

Run the unchanged pin and CPython 3.13.5 identity and error-order controls
with `python3.13 -I scripts/check-python-list-construction.py --upstream /path/to/pinned/rigorous`.

A checked tuple equality assertion can contain bound `__add__` on an
exact flat tuple literal or unbound `tuple.__add__` with two such positional
literals. The other operands are exact flat tuple literals or the addition
of two such literals. Every link must be equality and the checker validates the
whole chain. The runner evaluates reached operands from left to right
and carries the middle object into the next link. A false link or error
ends evaluation before the next operand.

The unbound path resolves the live module-first `tuple` binding and its
exact stock descriptor before preparing arguments. The separate
`legacyTupleSeed` supplies this type. The runners raise the defined missing
name and stop outside the profile for other bindings. The tuple evaluator
records the absent method on a `None` mask before preparing arguments.
The typed dispatch model returns the nonempty input when adding an
empty tuple, uses the empty singleton for two empty operands, and records
a fresh result for two nonempty inputs. Direct `__eq__` on an exact tuple
with a list returns `NotImplemented`, while operator equality returns
false. The source checker admits the exact `__add__` calls as tuple
operands. The evaluator's literal representatives and reached operands
are local to the assertion, and its equality compares scalar contents. The
existing caller namespaces, closure heap, list heap and generic call
receipts keep their separate observation rules.

The same assertion accepts `tuple()` and `tuple((...))` with one exact
flat scalar literal. The constructor resolves the live `tuple` binding
before preparing its argument. A missing binding raises `NameError`. A
modeled noncallable mask raises `TypeError` after argument preparation.
The stock descriptor delivers the canonical empty tuple or the exact
prepared object and reached tuple heap. The result keeps the argument's
address and incurs no second allocation. These addresses belong to the
assertion. Module tuple values carry scalar contents and require object
provenance before this constructor can accept them for identity-sensitive
use.

Run the unchanged pin and CPython 3.13.5 dispatch and sequencing controls
with `python3.13 -I scripts/check-python-tuple-chain.py --upstream /path/to/pinned/rigorous`.

A scalar comparison chain has at least two links. Every link uses one of
`==`, `!=`, `<`, `<=`, `>` or `>=` and every operand is an exact
Boolean or integer literal, including unary minus on an integer literal.
The checker validates the whole chain before folding. Each reached right
value becomes the next comparison's left value. The first false comparison
ends the scan. The result uses the same Boolean operand as a folded tuple
comparison, with no runtime lookup, call, or allocation.

Singleton identity has a separate checked chain for `is` and `is not`.
Each operand must produce `None` or an exact Boolean if evaluation succeeds.
This includes Boolean results of admitted scalar comparisons and nested
identity tests. The checker validates every link and operand, including a
suffix that execution will skip. The runners evaluate reached operands
left to right, carry the middle singleton into the next link, and stop at
the first false comparison or operand error. A successful test produces
a Boolean. Integer and text identities are outside this profile.

Reached operands of a checked `and` or `or` are Boolean or signed integer
literals. The source certificate records the first false value for
`and`, the first true value for `or`, or the last value at the end of
the sequence. A deciding operand permits the checker to use a separate
syntax check on the whole dead suffix. That grammar accepts integer,
Boolean and `None` literals, recursive unary and binary expressions, and
nested Boolean expressions with at least two operands. Names, calls,
and constructs introducing scopes are outside the dead-suffix grammar.
The module still runs full source scope analysis. A reached true division
remains an expression-profile rejection. Skipped true division has no
runtime instruction. The emitted result retains its integer or Boolean tag.

A closed `not` or assertion can also test `None` or a flat literal list or
tuple whose elements pass the scalar check. These tests use only falsity
or emptiness and emit no container value.

`None` can also be bound, read and copied as a module value. It has its
own tag and is false in a truth test. Scalar `==` and `!=` evaluate
their operands from left to right. Two `None` values compare equal, and
`None` compares unequal to an integer or Boolean. The integer
projection used by arithmetic and closed numeric chains applies to
integers and Booleans. Reached scalar arithmetic on `None` stops at the
arithmetic profile boundary. Object identity requires separate evidence
about the objects compared.

The regression emits Lean from Python source and verifies the global
access witnesses, action order and the diagnostic for an assertion
message.

The source runner accepts an initial namespace and builds the Core module
entry using the analyzed spelling of each name. Its correspondence law
matches the exact completion, visible trace and residual namespace.
The execution regression compares CPython and Lean on initialized reads,
overwrites, assertion failure, an unbound read and arithmetic failure.
[Runner contract](../../Silmaril/Languages/Python/Compile/ModuleEntry/Run/Thms.lean)

```sh
make check CHECK_TARGETS=+Silmaril.Languages.Python.Compile.ModuleEntry.Thms
make check CHECK_TARGETS=+Silmaril.Languages.Python.Compile.ModuleEntry.Run.Thms
```

## Function bindings and calls

The function plan keeps the source order of top-level assignments,
definitions and calls. A definition carries its analyzed child path,
fixed positional destinations and lowered body. Each call reads the
function by its module name and supplies ordered positional operands. The
result can be assigned to a name, discarded or tested by a message-free
assertion.

An implicit or declared global read in a function body retains its module
name. This supplies lookup in the namespace at call time, including writes
between a definition and call. Local references continue to use bounded
frame slots. The regression verifies both kinds of lookup.
[Function plan](../../Silmaril/Languages/Python/Compile/ModuleEntry/Functions/Thms.lean)

```sh
make check CHECK_TARGETS=+Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Thms
```

The module function runner links the selected bodies and publishes them in
the shared Core namespace, in source order. A positional call reads its
callable and its literal or name arguments through that namespace.
Positional arguments at a module call site may also be direct named calls
with literal or name operands. The ordinary runner saves the outer
callable in a frame local, evaluates each argument once from left to right
into separate locals, then invokes the saved callable. The result updates
the selected binding only on successful completion. The runner gives the
labelled invocation trace and a residual state that can be resumed with
further fuel. Its prefix composition theorem agrees with
a run using the combined fuel.

The adjacent keyword discard profile checks a bare call immediately
after its undecorated function definition. The definition has one required
positional-or-keyword parameter without an annotation. The call has one
`**` mapping literal with one string key and one integer literal value.
The key must equal the parameter's code points. The typed plan records
the adjacent publication and the one-slot argument mapping. The runtime
reads the live function binding and invokes it through the ordinary
positional executor with that integer. The seeded selector requires a
published function with one slot and records the ordinary completion
and reached heap. The call's result is discarded.

An undecorated module function can have one keyword-only parameter with
an integer literal default when its body is a single message-free assertion
comparing that parameter to an integer literal. The checked linked entry
retains the literal and accepts zero positional arguments. After the
ordinary binder accepts omission, a store initializes the parameter's
local slot without touching the heap. A call through an alias uses its
function's own saved literal. Seeded discard uses its existing published
zero-argument selector and settlement rule. Explicit positional values
fail ordinary arity checking. Explicit keyword arguments, dynamic
defaults, and introspection of these defaulted definitions are outside
this profile.

Checked function bodies can add and multiply integer literals and values
read from fast locals, owned or forwarded cells, and live module globals.
The operations can nest. The executor reads the left operand and then the right operand
before checking their types. Booleans contribute 0 or 1 and the result is
an integer. A plain function or `None` operand raises `TypeError` after
both reads succeed. This value profile covers integer arithmetic without
custom operator methods or sequence concatenation. The ordinary and Finite
runners share operand evaluation, and the seeded runner uses it when an
existing selector admits the call.

At module call sites, deeper argument nesting, arithmetic operands,
and keyword or unpacked arguments outside the adjacent discard shape
are rejected. The seeded runner supports these
nested instructions within its [closed call profile](python-seeded-module-runner.md).
The CPython regression checks
result placement, lookup and argument error order, and residual bindings.
The Lean regression also checks the call-entry order across a live prefix.
The ordinary module runner also accepts a message-free `assert not test`
when `test` is an existing module operand. It evaluates the operand once,
propagates evaluation errors, and succeeds exactly when the result is
false by the ordinary truth rule. This includes a name bound to a
returned `None`. The seeded runner also handles this instruction for
its existing [seeded operands](python-seeded-module-runner.md).
[Module-call runner](../../Silmaril/Languages/Python/Compile/ModuleEntry/Functions/Run/Thms.lean)

```sh
make check CHECK_TARGETS=+Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Thms
```
