# Core entry semantics

[`Entry.Defs`](../../Silmaril/Wasm/Execution/Core/Entry/Defs.lean) uses the unchanged
[`HasOpSem`](../../Silmaril/Semantics/Operational/Policy/Defs.lean) interface at three boundaries:

| Boundary | Entry | Execution |
| --- | --- | --- |
| Module instantiation | `Instantiate` with already-resolved external addresses, in import order; `typedModule` additionally takes an intrinsic module, a typed store, and typed imports | Actual Core `Step` for segments and start; `ReadyAfter` publishes the allocated module with the **post-start** store only for `.values []` |
| Named ready export | `Game.Accept.exportFunc?` on the allocated module, then Core `invoke`; `ResolvedExport` checks that the name picks the address of a `DirectCall` | Actual Core invoke for raw entry, existing independent intrinsic execution for typed entry |
| Ready scalar instance | `ScalarInstance.initThread` at the supplied **current** store; `typedInstance` checks the selected body at a well-formed registration and admits matching typed requests | Host-free Core phase versus intrinsic body; `session_finishes_iff` compares a resolved finite execution to the actual store-retaining `instFinS` |

Import name resolution is a caller responsibility, not a reduction of this
machine. Instantiation includes validation, allocation and initializer evaluation
before segment/start reduction begins. Bad or missing resolution and a missing
named export supply **no entry**; they do not produce a trap or UB. Typing does
not assert that initialization succeeds or that start terminates. No empty-import
claim is made about arbitrary unrelated stores.

## Ordinary, policy-gated, and restricted

`ordinary` has actual Core steps, terminal values/throws/traps, and no UB
relation. The raw `policy` adds UB when `ConfigOk` fails at the selected result
type, without interpreting a missing host answer or absent observation as UB.
Its `toOpSem` only forgets the UB tag; it **keeps** the policy's gated transitions.
`typedModule` instead **restricts** to the subtype of `ConfigOk` states. The
[`entry theorems`](../../Silmaril/Wasm/Execution/Core/Entry/Thms.lean) use Core
preservation under `HostOk` to recover all ordinary finite outcomes after this
restriction; the host-free invocation proof uses preservation only, not host
progress. The intrinsic entry machines already have no UB predicate other than
`False`. `Finishes` retains the final configuration, including the store after
a trap or throw; `Outcome.trap` itself has no payload. `invoke_finishes_iff` reads
back the exact final store and frame of this integer/local fragment. It does not
assert that other Core invocations preserve their stores.

## Checked registration, not component composition

The [regression](../../tests/wasm/module-entry/Regression.lean) validates and
instantiates a real import-free Core module, then uses its allocated `divide`
export in a well-formed `NumInstance`, the ready Core leaf used by the component
denotation. It checks `84 / 7 = 12`, a divide-by-zero trap with the exact return
store, missing lookup, and fuel exhaustion before the finite result. The session
theorem needs a finite typed answer and the registered address, arguments and
answer to agree; it then excludes `.div` for that activation. Outer `none` from
`runFor` is not evidence of divergence.

This does not replace linked component execution. The existing
[`denUD_core3SemD_eq_of_related_stores`](../../Silmaril/Wasm/Execution/Core/Intrinsic/Invoke/Session.lean)
requires `RoundEq (instTripleS …) (instTripleS …) rel s t` **for every related
store pair**: re-establish the store invariant after values and traps, match
finite import/answer logs and divergence, and match pending calls and productive
streams. In a linked execution the invariant must also account for allocation
prefixes and import address resolution. The one-activation proof here supplies
none of those linking or prefix obligations. Nor does it compare the IR's
`Comp.denUD` to the reference runtime's
[`exportBehaviours`](../../Silmaril/Wasm/Component/Reference/Defs.lean), which
instantiates a component before dispatch and observes traps or divergence during
that phase too. [`IntrinsicWiring.Program.sound`](../../Silmaril/Wasm/Component/IntrinsicWiring/Thms.lean)
checks wiring validity, not that execution correspondence.

```sh
make check CHECK_TARGETS=+Silmaril.Wasm.Execution.Core.Entry.Thms
```
