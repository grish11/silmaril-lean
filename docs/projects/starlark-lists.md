# Starlark collection store

The store follows the same Bazel-team core dialect as the scalar API, at
specification commit `c0af0ea03dc90d3bbc021394b693e6957cc15030` (2026-02-06).
The SHA-256 of the raw `spec.md` is
`9e1e2b52717512968270bc99ca79aa8c9014df99a9befd0b47eed59c7c848597`.
[Specification][spec] · [Scalar API](starlark.md)

## Supported code and observations

`Silmaril.Languages.Starlark.Lists.Thms` exposes the resolved code, store,
denotation and operational rules. Resolved expressions cover three families.

- Scalar values `None`, Booleans and exact integers, with resolved binding reads.
- List, tuple and dictionary displays, with arbitrary nesting. The compiler-facing
  dictionary entry spine builds from earlier entries to later entries.
- Subscript reads from lists, tuples and dictionaries, and the one-argument
  list method `append`.

The statement forms are name and subscript assignment, evaluation for effects,
`pass`, and sequencing. `Lists.Iteration.Thms` adds function-body conditionals,
single-name `for` over these three container types, `break`, `continue` and
`return`. A bare return lowers to the scalar value `None`. The suite index
counts lexical loop depth and rules out unscoped `break` and `continue`.
Callers supply resolved binding slots and enforce source rules such as
single-assignment globals and function-only control. The scalar entry points
and theorem signatures from #2144 remain source-compatible.
[Code and store](../../Silmaril/Languages/Starlark/Lists/Defs.lean) · [Suites](../../Silmaril/Languages/Starlark/Lists/Iteration/Defs.lean)

An allocation gives each collection a fresh address in one heap. Name
assignment copies values and therefore preserves references. Address numbers
are internal to a particular heap. A future shared-syntax agreement theorem
can compare effects under a correspondence of reachable addresses.
Tuple fields are immutable, and a tuple can hold a reference to a mutable
collection. That collection can be updated through the reference.
[Identity][identity] · [Lists][lists] · [Tuples][tuples] · [Dictionaries][dicts]

List and tuple indexes accept integers in `[-length, length)`, with negative
indexes measured from the end. List and tuple elements evaluate left to right.
Indexed assignment evaluates its RHS before its receiver and index.
`append` selects the method on the receiver before evaluating its argument and
checks mutability after argument evaluation. A successful append returns
Starlark `None`. A failure retains the state reached by the preceding
operands. Error tags carry the relevant failure kind and may include the
index, address, key, or binding. A bad address or an address of the wrong
kind is a model error for malformed host-supplied states. Resolved code has
no address literal.
[Subscripts][index] · [Assignments][assign] · [Denotation](../../Silmaril/Languages/Starlark/Lists/Denotation/Defs.lean)

## Dictionary keys and order

Dictionary displays evaluate each key and then its value. The pair is checked
for admissibility and duplicates before evaluating the next pair. A subscript
write inserts a missing key at the end or updates the value in place, keeping
the original key and position. A missing subscript read fails.
`putEntry_keys` proves the resulting order of keys for both insertion and
replacement. The model uses an ordered list of entries.
[Dictionary expressions][displays] · [Dictionaries][dicts] · [Theorems](../../Silmaril/Languages/Starlark/Lists/Thms.lean)

Key comparison uses tagged scalar values and structural tuple contents. A
tuple's cached encoding brackets the encodings of its elements and is present
when every element has a key encoding. Separately allocated tuples with equal
contents hit the same entry. Boolean and numeric keys are distinct. List and
dict keys are rejected even when frozen, matching the pinned starlark-go
profile. The general prose spec allows for frozen mutable keys, so this policy
is explicit. The model covers the admissibility and equality needed by the
dictionary operations. The `hash` built-in and general value equality remain
open. Public raw heap constructors can supply malformed key caches. The
normal expression evaluator computes them on allocation.
[Lists][lists] · [Hashing][hashing] · [Pinned oracle][go]

## Reachable freezing

`State.freeze` is a host operation supplied with root values. It represents
the freezing part of publication. Module initialization and root selection are
outside this API. The reachable graph follows list and tuple elements and both
keys and values of dictionary entries. The implementation finds each selected
address at most once. Shared references, self-cycles, and cycles across
collection kinds all use this reachability policy. The heap keeps all addresses
and contents, and previously frozen cells stay frozen. Unreachable mutable
cells stay mutable. Reads continue to work through any alias.
[Freezing][freeze] · [Freeze definitions](../../Silmaril/Languages/Starlark/Lists/Freeze/Defs.lean)

`freezes_iff_freeze` independently characterizes the operation by live graph
reachability and the pointwise update on the original heap, for every finite
heap. `keyOf_freeze` proves that freezing preserves key eligibility and
encodings. `editCell_frozen` proves that a frozen cell rejects an edit with
its incoming state intact.
[Theorems](../../Silmaril/Languages/Starlark/Lists/Thms.lean)

## Iteration and control

A loop evaluates its iterable once, captures its finite sequence, and acquires
an iterator for the address. Lists and tuples iterate over elements and
dictionaries iterate over insertion-ordered keys. List edits and dictionary
writes reject an active mutable address, so the guard applies through all
aliases. The frozen check retains priority over the active check. List
index validation precedes the write guard. Dictionary writes check
mutability before validating key admissibility, as in the Go oracle. The stack
has one entry per active iterator, including repeated entries for the same
object. Continue retains the entry until loop exit. Exhaustion, break, return
and error release the entry while retaining effects already performed. Nested
loops restore their incoming stack. The suite evaluator recurses on syntax
and its iterator recurses over the captured finite sequence. Neither takes
execution fuel or bounds nesting.
[Iteration][iteration] · [For statements][for] · [Break and continue][break]

`eval_iff_denote` and `runs_iff_denoteSuite` prove exact agreement between the
respective denotations and independent big-step rules on success and failure,
including the resulting state. The rules share lexical and heap primitives
and independently order their premises. `iterators_denoteSuite` proves
restoration of the original iterator stack for every suite exit.
`editCell_iterating` states the active-iterator mutation guard.
[Expression rules](../../Silmaril/Languages/Starlark/Lists/Operational/Defs.lean) · [Suite rules](../../Silmaril/Languages/Starlark/Lists/Iteration/Operational/Defs.lean) · [Suite theorems](../../Silmaril/Languages/Starlark/Lists/Iteration/Thms.lean)

## Reproduction

```sh
lake build --wfail +Silmaril.Languages.Starlark.Checks +Silmaril.Languages.Starlark.Lists.Checks \
  +Silmaril.Languages.Starlark.Lists.Iteration.Checks +Silmaril.Languages.Starlark.Lists.DictionaryChecks
```

The kernel-checked fixtures cover addresses and aliasing, transitive freezing,
cycles, indexing and mutation failures, tuple keys, duplicate-key evaluation
order, insertion order, and iterator guards and cleanup. The Go fixtures use
`Program.Init` to observe state before publication and freeze selected roots.
Host appends and dictionary writes after a failed Starlark call test cleanup.
The reference is starlark-go at commit
`4f4267fb140d1e8b91c9bce55cee2f809e8840dd` with default syntax options. The
huge-index case compares failure only because Go reports its 32-bit conversion
limit.
[Lean fixtures](../../Silmaril/Languages/Starlark/Lists) · [Go fixture](../../examples/starlark/list-store/check.go) · [Pinned oracle][go]

Run the Go fixture from the public oracle checkout using Go 1.25 or newer.
Start these commands from the Silmaril repository root.

```sh
fixture="$(pwd)/examples/starlark/list-store/check.go"
oracle="$(mktemp -d)"
git clone https://github.com/google/starlark-go.git "$oracle"
git -C "$oracle" checkout --detach 4f4267fb140d1e8b91c9bce55cee2f809e8840dd
(cd "$oracle" && go run "$fixture")
```

## Remaining work

- **Functions.** User function objects, lexical cells, calls
  and declaration-based recursion checks extend this store. The call profile
  includes definition-time defaults, keyword-only parameters and both
  argument expansions. Calls inside collection loops and source lowering
  remain open.
  [Lexical calls](starlark-functions.md) · [Functions][functions]
- **Collection operations.** General equality and ordering, `len`, `hash`,
  concatenation, slicing, comprehensions, other methods, augmented assignment,
  destructuring, and other iterable types remain open. The supported
  collection truth tests apply in the resolved suite conditional.
- **Module initialization and loading.** Run each module with its own lexical
  frame and host thread context. Select all global roots on successful
  publication, including private globals, and preserve heap identities in
  the loader cache. Export validation, dependency cycles, load failure and
  host policies remain open. [Module execution][modules] · [Load statements][loading]
- **Source front end.** Parsing, shared Python and Starlark syntax resolution,
  and the Lean quotation macro remain open.

[spec]: https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md
[lists]: https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#lists
[tuples]: https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#tuples
[dicts]: https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#dictionaries
[displays]: https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#dictionary-expressions
[identity]: https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#identity-and-mutation
[index]: https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#subscript-expressions
[assign]: https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#assignments
[freeze]: https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#freezing-a-value
[iteration]: https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#iteration
[for]: https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#for-statements
[break]: https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#break-and-continue
[hashing]: https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#hashing
[functions]: https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#functions
[modules]: https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#module-execution
[loading]: https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#load-statements
[go]: https://github.com/google/starlark-go/tree/4f4267fb140d1e8b91c9bce55cee2f809e8840dd
