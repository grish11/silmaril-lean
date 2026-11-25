# Starlark lexical calls

The core dialect follows the Bazel team's specification at revision
`c0af0ea03dc90d3bbc021394b693e6957cc15030`, with raw `spec.md` SHA-256
`9e1e2b52717512968270bc99ca79aa8c9014df99a9befd0b47eed59c7c848597`.
[Functions][functions] · [Name binding][names] · [Definitions][defs]

## Resolved input

`Silmaril.Languages.Starlark.Functions.Thms` exposes function definitions,
calls, sequencing, conditionals and the
existing total collection suites. Calls in expression position lower to calls
with fresh destination slots. The current collection suites can be lifted as
single blocks, including their local loops, writes and returns. Lifting
preserves the collection denotation exactly. This normalized input requires a
finite declaration table. The caller supplies statically resolved names and
scope legality, including full lists of local slots and free names. Calls
inside collection loop bodies are outside this profile.
[Definitions](../../Silmaril/Languages/Starlark/Functions/Defs.lean) · [Theorem header](../../Silmaril/Languages/Starlark/Functions/Thms.lean)

Each invocation allocates its own lexical slots. A closure keeps the
addresses of free slots from its defining activation or module. It can
therefore observe later assignments to those slots, even after that activation
returns. The callee's capture slots are read-only, and assigning a local does
not rebind an outer scope. Slot tables and bindings return to the caller on
success and failure. Heap effects survive both exits. Functions with no
explicit return yield `None`. The shared heap keeps function identities and
uses those identities for function keys.
[Functions][functions] · [Definition and invocation primitives](../../Silmaril/Languages/Starlark/Functions/Defs.lean)

Freezing follows local captured cells, including a function stored in its
own captured slot. Defining-module globals are distinct from local captures.
The pinned Go implementation freezes them at module publication; a standalone
function freeze follows its local captures. The host boundary must supply
global roots when publishing a module.
[Module execution][modules] · [Pinned Go runtime][go-function]

## Termination and observations

A function's declaration index is stable across its closure instances.
An invocation rejects any declaration that is active already, even through a
different closure instance. Recursion detection precedes parameter binding.
The entry point starts with all declarations available. Descent removes every
matching declaration from the available set, while sequencing and branching
descend into smaller syntax. The underlying collection loops use finite
snapshots. There is no fuel or resource error in this profile. It assumes a
fixed finite declaration table and omits host callbacks and options enabling
recursion. A later semantics with such callbacks or options needs a separate
account of divergence and host observations.
[Denotation](../../Silmaril/Languages/Starlark/Functions/Denotation/Defs.lean) · [Recursion][functions]

The independent big-step rules compose collection-expression and suite
judgments with call entry and exit. The adequacy theorem covers exact results,
errors, caller restoration and the remaining shared store. Frames and heap
addresses are internal to the Lean model. The Go checks observe values,
aliasing, recursion rejection and heap effects through the host API.
[Operational rules](../../Silmaril/Languages/Starlark/Functions/Operational/Defs.lean)

## Argument binding

A resolved signature has positional-or-named parameters, keyword-only
parameters, and optional `*args` and `**kwargs` slots. Default expressions
evaluate left to right in the defining activation. Each new closure stores
their values once, and publication freezes them through the same heap
reachability rules as captured cells. Filling an omitted argument uses the
stored value, so mutable defaults share identity across calls.

The resolved call form represents positions, named operands, at most one
`*`, and at most one final `**`. All operand expressions evaluate left to right
before expansion. The supported `*` sources are lists, tuples and dictionary
keys. The supported `**` source is a dictionary with string keys. Expansion
preserves dictionary insertion order. When both expansions are invalid the
Go profile checks `**` first, after both operand expressions have run. A
call checks re-entry before binding parameters.

Binding checks positional overflow, assigns keywords in appearance order,
and fills omitted parameters from defaults. It reports duplicate assignment,
unexpected keywords and the missing required names. Fresh tuple and
dictionary packs are allocated only after successful binding. They enter
the activation by reference just like the other argument values. String
values support literal content, truth and key comparison in this profile.
Other string operations and additional star iterables remain open.

`runChecked` validates all normalized parameter lists and call sites before
executing, including unreachable call sites. It rejects duplicate parameter
names and repeated explicit keywords. The ordering of positional parameters
and expansion sites is enforced by their representation. A required
positional parameter cannot follow one with a default. The pinned prose
requires an optional keyword-only parameter after a bare `*`. The pinned
Go implementation accepts a required-only keyword signature, which the
fixture records as a difference. The caller still supplies lexical resolution
and valid identifier spellings, and lowers call expressions within operands
to ordered calls and temporary slots.
[Argument binding](../../Silmaril/Languages/Starlark/Functions/Arguments/Defs.lean) · [Functions][functions] · [Definitions][defs]

## Checks and extensions

```sh
lake build --wfail +Silmaril.Languages.Starlark.Functions.Checks \
  +Silmaril.Languages.Starlark.Functions.Arguments.Checks
```

Use Go 1.25 or newer and run from the repository root.

```sh
fixture="$(pwd)/examples/starlark/functions/check.go"
oracle="$(mktemp -d)"
git clone https://github.com/google/starlark-go.git "$oracle"
git -C "$oracle" checkout --detach 4f4267fb140d1e8b91c9bce55cee2f809e8840dd
(cd "$oracle" && go run "$fixture")
```

Module initialization, prepublished imports and five universal built-ins
extend this profile. Host callable effects remain open.
[Modules](starlark-modules.md) · [Built-ins](starlark-builtins.md)

The next loop slice can index resolved function bodies by loop depth and
reuse the existing snapshot and iterator cleanup rules. A loop body can
then evaluate a call into a fresh local slot and use that slot in later
statements or the return. The proof should cover aliased mutation through
a callee and cleanup on break, continue, early return and failure. This
gives a target for lowering calls in expression position, starting with
ordered operands and preserving branch-dependent evaluation.
[Collection loops](starlark-lists.md#iteration-and-control)

[functions]: https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#functions
[names]: https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#name-binding-and-variables
[defs]: https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#function-definitions
[modules]: https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#module-execution
[go-function]: https://github.com/google/starlark-go/blob/4f4267fb140d1e8b91c9bce55cee2f809e8840dd/starlark/value.go
