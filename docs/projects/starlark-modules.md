# Starlark module publication and imports

The profile follows the Bazel-team core specification at
`c0af0ea03dc90d3bbc021394b693e6957cc15030`. Raw `spec.md` has SHA-256
`9e1e2b52717512968270bc99ca79aa8c9014df99a9befd0b47eed59c7c848597`.
[Module execution][modules] · [Load statements][loading]

`Silmaril.Languages.Starlark.Modules.Thms` exposes the resolved entry point
`initializeModule`. It checks argument-list legality and conflicting global
and file names before allocating slots. It executes top-level commands in
order. The supported commands are collection assignments and expression
statements, resolved definitions and calls, and load statements with named
aliases. Function-only control lives within declarations. Clients supply
declared globals and resolved assignments, including single assignment of
explicit globals and legal load identifiers. Temporary slots used by call
lowering and file-local imports remain outside the global export list.
[Definitions](../../Silmaril/Languages/Starlark/Modules/Defs.lean)

The host supplies a pure catalog of already published modules. It determines
how labels are interpreted. All modules in a catalog share the same heap
and the same linked function-declaration table. An imported value retains
its address, so calling an imported closure uses that closure's original
global slots. A missing catalog entry and a missing exported name are
distinct failures. Private import names are rejected during validation.
A single load resolves all its requested exports before binding their aliases.
[Load statements][loading] · [Lexical calls](starlark-functions.md)

A new module begins with fresh slots and no inherited active iterators.
Successful completion freezes all global values, including private ones,
before publishing the public export table. Runtime failure returns the
updated heap with the caller's scope and iterator context restored. The
failure path publishes no module and performs no publication freeze.
A caller supplies both the initial heap and any prepublished imports.
The heap may retain unreachable allocations.
[Module execution][modules] · [Reachable freezing](starlark-lists.md#reachable-freezing)

`initializes_iff_initialize` proves exact agreement with independent
command-sequencing and initialization rules on publication, failure and final
state. Core top-level commands use the existing independent function and
collection judgments. The rules use the same host catalog contract as the
denotation. Effectful loading, recursive dependency discovery and execution,
cycle errors, host thread callbacks and source parsing remain open.
[Operational rules](../../Silmaril/Languages/Starlark/Modules/Operational/Defs.lean) · [Theorem header](../../Silmaril/Languages/Starlark/Modules/Thms.lean)

The next loader slice can use a finite in-memory manifest with a
requester-relative label map to canonical module IDs. Resolve each load
when its command runs, initialize unseen modules on demand, and memoize
successful publication. Track active IDs to report dependency cycles.
The fixtures should distinguish a shared dependency reached by two labels
from a cycle, and check propagation of a dependency failure with prior
heap effects. Module resolution and cache policy in this slice are host
choices. Filesystem access, host callbacks and failure caching can stay
outside the manifest model.
[Load statements][loading] · [Module execution][modules]

The Lean fixtures cover cross-module captures, private freezing, file-local
aliases, validation, missing exports and rollback of the scope on failure
while retaining prior effects. The pinned Go fixtures compare successful
publication, import observations and failure categories. They use Go's
`ExecFileOptions` success path for publication. The Lean-only failure fixture
asserts the absence of a publication freeze after failure, following the
prose spec. Go's convenience wrapper also freezes the partial global mapping
on error.
[Lean fixtures](../../Silmaril/Languages/Starlark/Modules/Checks.lean) · [Go fixtures](../../examples/starlark/modules/check.go) · [Pinned starlark-go][go]

```sh
lake build --wfail +Silmaril.Languages.Starlark.Modules.Checks
```

Use Go 1.25 or newer and run from the repository root.

```sh
fixture="$(pwd)/examples/starlark/modules/check.go"
oracle="$(mktemp -d)"
git clone https://github.com/google/starlark-go.git "$oracle"
git -C "$oracle" checkout --detach 4f4267fb140d1e8b91c9bce55cee2f809e8840dd
(cd "$oracle" && go run "$fixture")
```

[modules]: https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#module-execution
[loading]: https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#load-statements
[go]: https://github.com/google/starlark-go/tree/4f4267fb140d1e8b91c9bce55cee2f809e8840dd
