# Import Quint exports into General TLA

The [import header](../../Silmaril/Logic/Temporal/TLA/Import/Defs.lean)
reads complete TLA+ source through the native parser and scalar elaborator.
The caller supplies the flexible variable sorts, standard library identities,
and names of the initial and step operators. Every declaration is checked
before the two operators are selected.

## Export and import a module

The fixture [setup and reproduction guide](../../tests/semantics/tla-quint/README.md)
pins Quint 0.34.0 at `95141d4691cce7e60104bdfcbc1d1b074f1cb789` and
Apalache 0.62.4 at `7954daf7563a69cce9d0b89c8542e40bf46f7c6e`. With that
setup, export with the following command, using a fresh loopback port for
the pinned backend.

```sh
node "$quint_checkout/quint/dist/src/cli.js" compile Model.qnt \
  --target=tlaplus --main=Model --init=init --step=step \
  --apalache-version=0.62.4 --server-endpoint="127.0.0.1:$port" --verbosity=0 > Model.tla
```

Pass the exported file as UTF-8 source. `Profile.quintApalache0624` selects
`q_init` and `q_step` and makes the six pinned standard module identities
available. The caller attests that the module's `EXTENDS` names resolve to
those libraries without local replacements. The profile supplies
`Integers` for arithmetic and `Apalache` for `:=` when the module names
them in `EXTENDS`. `:=` denotes same-sort equality on a fixed pair of
states. A primed expression reads the target and an unprimed expression
reads the source. [Elaborator contract](tla-elaborator.md) ·
[Pinned Apalache definition](https://github.com/apalache-mc/apalache/blob/7954daf7563a69cce9d0b89c8542e40bf46f7c6e/src/tla/Apalache.tla)

```lean
module

import Silmaril.Logic.Temporal.TLA.Import.Defs

open Silmaril.Logic.Temporal.TLA

def counterProfile : Import.Profile := .quintApalache0624 [("n", .int)]

def readCounter (path : System.FilePath) :
    IO (Except Import.Diagnostic (Import.StateAction counterProfile.signature)) := do
  let source ← IO.FS.readFile path
  return Import.importModule counterProfile source
```

For [BoundedCounter](../../tests/semantics/tla-quint/BoundedCounter.tla), use
`counterProfile`. For [BitPair](../../tests/semantics/tla-quint/BitPair.tla),
use `Profile.quintApalache0624 [("x", .int), ("y", .int)]`. The explicit
sorts supply the information shown in the exporter’s `@type` comments.
On success `imported.initial.toStatePred` and `imported.step.toAction` give
the General TLA meanings. Apply them with `profile.signature.noRigid` and
valuations indexed by name and sort. The two kernel predicates also supply
executable decisions. Standard TLA+ source can use the same API with its
own profile. The [native latch](../../tests/semantics/tla-quint/Latch.tla)
uses one Boolean variable, no libraries, and `Init` and `Next`.

`Import.Diagnostic.parse` includes a source span and message. The
`elaborate` case carries the elaboration reason and, for errors in
definition bodies, the definition name. The `initial` and `step` cases
identify the selected operator and the reason it could not be used.
[Parser diagnostics](tla-parser.md) · [Elaboration fragment](tla-elaborator.md)

## Bounded checks and stuttering

```sh
make tla-import-check
```

This target runs in `make check` for the TLA+ import path. With the pinned
Lean toolchain and Lake dependencies in place, it needs no Node, Java, or
network access. It checks the original fixture and oracle hashes, reads the
export bytes directly, and compares the complete initial set and raw
relation on the supplied state lists. Oracle columns follow `variables`
and map to the imported scope by name.

| Fixture | Initial candidates | Ordered pairs | Accepted initial states | Accepted raw pairs |
| --- | ---: | ---: | ---: | ---: |
| BoundedCounter | 3 | 9 | 1 | 2 |
| BitPair | 4 | 16 | 1 | 8 |

The harness uses `Kernel.Bounded.mem_initials` and
`Kernel.Bounded.mem_transitions` to certify that list membership agrees
with the imported General TLA denotations on the given domain. The
counter has no raw successor at `2`. A separate check calls
`imported.step.bracket` with the observation of its sole coordinate
`n`. This explicit full-state bracket adds each diagonal pair, including
`2 → 2`. [Kernel adequacy](tla-semantic-kernel.md) ·
[Regression harness](../../tests/semantics/tla-quint/Import.lean)

The exact bounded comparisons cover these two pinned exports. The source
fragment accepts scalar state predicates and raw actions. Temporal
specifications, action brackets in source, fairness, user libraries,
composite values, and proof checking remain outside this import path.
The checks leave general exporter correctness, reverse translation,
unbounded graph equivalence, and temporal equivalence open.
[Syntax coverage](tla-parser.md) · [Semantic coverage](tla-elaborator.md)
