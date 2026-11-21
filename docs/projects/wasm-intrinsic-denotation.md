# Denotation of registered intrinsic Core Wasm

The [game bridge](../../Silmaril/Wasm/Game/Intrinsic/Thms.lean) interprets intrinsic
functions and modules without adding a Core execution relation. A `Registered`
module fixes the actual `CModuleType` of an intrinsic module and gives a
start-free `IsInstance` of its erasure, with the function-only scalar export
interface checked in order. An `Entry` selects an export whose store slot
contains the *exact erased function*, not just a matching signature.

```text
intrinsic function ── erase + checked address ──▶ Core invoke at the current store
       │                                                 │
       │ typed scalar export question                    │ Core steps / divergence
       ▼                                                 ▼
open instance game ── compose with Env; observe ──▶ set of Core behaviours
```

- `Entry.invokeOk` and `Entry.enter` link typed arguments to the actual Core
  invocation and its first reduction into the frame with the erased body.
- `Entry.adequacy` and `Registered.adequacy` prove equality of behaviour sets:
  sound and complete for returns, traps, uncaught exceptions and may-divergence.
  The profile is arbitrary. The host must be `hostOf` a game `Env`, which
  leaves the store unchanged on return; `ThrowsBelow` bounds its exception
  answers. The current store must satisfy `ScalarInstance.WellFormed` (provided
  by `IsInstance.ok` at the module's initial store). Different branches may
  both terminate and diverge. An absent host answer may diverge, not trap.
- `Entry.first_import_iff` reads the first import move in both directions from
  the stock host-free Core run and its callout. `Entry.round_iff_activation`
  and `Entry.continue` retain the actual import moves and post-round store
  (also after a trap). These use the open game's `Path` and strategy, and do
  not infer open equality from the closed theorem. Later unanswered calls and
  unbounded silent activity belong to the enclosing `DStrategy`.
- The bridge starts **after** registration. Instantiation, start/segment
  outcomes, import resolution, and linking to a named export are separate
  obligations; see [Core entry semantics](wasm-opsem-entry.md), including
  `ReadyAfter` and `ResolvedExport`. Lifting to components via store replacement
  needs `RoundEq` for every related pair of stores (re-established after each
  result/trap), pending calls, productive streams and divergence, not merely
  a closed observation comparison.

The [module regression](../../Silmaril/Wasm/Game/Intrinsic/Examples.lean) reifies
and instantiates one module with an imported callback and three exports: an
ordinary return, a division-by-zero trap, and a call whose first import move
is checked against the actual Core redex.

## Ultrastrict numeric suffix contexts

The separate [numeric model](../../Silmaril/Wasm/Execution/Core/Intrinsic/Pure/Thms.lean)
interprets the stock intrinsic integer `Code` as a total function from typed
arguments to `Option (Values results)`. Declared integer locals start at zero;
argument and local order is the Core order, and result order is reversed from
the machine's top-first stack at observation. `none` means trap, not exhaustion
or divergence. An integer division trap prevents the suffix from executing.

`invoke_denotes` proves the **entire** stock Core behaviour set is a singleton
for any resolved `DirectCall` and deterministic profile `profile oracle`,
under `noHost`. For `postEquivalent_iff`, a context appends the same typed
straight-line suffix to each alternative, links each completed function into
a well-formed Core store at its actual address, and invokes with any Core-valid
arguments. The denotation is defined independently of those tests. Equality
implies equal observations by sequential evaluation; the empty suffix and
injectivity of Core result readback give the converse at linked base terms.
Other Core contexts, calls in bodies, mutation, allocation, references and
recursion are not in this theorem. The [regression](../../Silmaril/Wasm/Execution/Core/Intrinsic/Pure/Examples.lean)
checks an ultrastrict (import-free) numeric module, subtraction order, division trap, and a
nonempty suffix. It distinguishes the trapping and nontrapping programs while
equating subtraction with the same code preceded by `nop`.

The landed `Strict.toFunctional` keeps the raw Core AST unchanged; this does
not compare different operational semantics. The current `Profiles.Strict`
checker requires no imports; the semantic design uses **Strict** for the
import-capable fragment and **ultrastrict** for the import-free scope of the
numeric theorem. Neither admission policy nor the sibling syntax API is changed
here. No version-category claim follows.
A larger functional fragment can still allocate immutable objects, diverge,
or expose an equality test on suitable opaque references. The actual Core
`struct.new` allocates fresh references and `ref.eq` can observe identity of
allowed references; removing mutation alone does not make such observations
extensional in the function's input/output mapping. No addresses are exposed
as numbers. A GC extension would need an invariant relating allocated heaps
and a precise restriction on the permitted reference observers.

```sh
make check CHECK_TARGETS='+Silmaril.Wasm.Game.Intrinsic.Examples +Silmaril.Wasm.Execution.Core.Intrinsic.Pure.Examples'
```

## Named import requests and replies

[`Requests.Tree`](../../Silmaril/Wasm/Game/Intrinsic/Requests/Defs.lean) is a
well-founded request/reply computation, independent of the game observer. A request
points at the actual raw import declaration and carries a typed argument list;
the continuation receives an `Answer` for that import's signature. Matching
goes through the ordered scalar slot of the registered instance, not through
string equality. A result, trap, and thrown address are distinct leaves.

```text
typed tree ── Completes (admissible replies) ──▶ visible import/reply/answer trace
    │ Realizes (host-free Reach + actual resumption)              │ same moves
    ▼                                                           ▼
erased intrinsic entry ── stock Core instance game ────────▶ completed Entry.round
```

[`Realizes.path_of_completes` and `completes_iff_entry_round`](../../Silmaril/Wasm/Game/Intrinsic/Requests/Thms.lean)
prove soundness for any profile with realization evidence, and exact completed
single-entry traces under `profile oracle` for plays satisfying
`PlayThrowsBelow n`. The proof retains the game path to its actual post-call
store; the tree does not compute that store or establish a relation between
arbitrary stores. The implementation evidence is per reply: the callout must
resolve to the same slot with the same arguments and the continuation starts
at the real `resumeResult` thread. The concrete fixture certifies validity of
the bound (`n = 0`, empty exception store).

`Tree.handle` is a **separate** partial, memoryless, store-preserving host
interpretation (`Env`/`hostOf`), not a restriction on imports. Under
`ThrowsBelow env n`, `Realizes.handled_mem_core` gives membership in the stock
Core behaviour set. For a registered or otherwise well-formed entry, with
`ThrowsBelow env store.exns.length`, `handled_mem_entry` gives membership in
the stock divergence-observing game. A missing reply witnesses a Core
stuttering trace at the callout, not a trap. These membership results do not
exclude other behaviours at a nondeterministic profile.

The [regression](../../Silmaril/Wasm/Game/Intrinsic/Requests/Examples.lean)
reifies, validates and instantiates an export that asks `env.callback(7)`;
an empty reply continues to `i32.const 42`, a trap reply propagates a trap,
and a silent host diverges. The round proof does not choose a host. This is
not a whole-Strict interpreter or full abstraction: the well-founded tree cannot
represent recursive silent divergence or infinitely many answered requests;
those need a productive model and a simulation against the existing silent
and infinite game runs. Mutation-free Wasm can still have observable host
effects; stateful and store-changing host transfers require separate evidence.

```sh
make check CHECK_TARGETS='+Silmaril.Wasm.Game.Intrinsic.Requests.Examples'
```

### A guarded answered-import loop

The [single-back-edge bridge](../../Silmaril/Wasm/Game/Intrinsic/Requests/Repeat/Thms.lean)
checks a cyclic case the well-founded tree cannot express. After a typed
successful reply, the stock host-free machine must reach *exactly* the same
store and callout thread. `Repeat.periodic_core` exhibits one infinite Core
trace with a positive period, with an actual store-preserving host return
at each period boundary. It assumes the typed `Env` gives the selected
reply and uses `hostOf`; it does not turn missing replies into successful
steps. `Repeat.game_prefix` separately constructs every answered-prefix
length in the open game, retaining the next pending callout.

The [intrinsic loop regression](../../Silmaril/Wasm/Game/Intrinsic/Requests/Repeat/Example.lean)
calls `env.tick(7) : i32` and uses `br_if 0` on the reply: `1` restarts the
loop; `0` completes the export. The repeating case also observes divergence
in the stock composed game, with initial store well-formedness and bounded
exceptions via `Entry.adequacy`. The Wasm body uses no mutation or allocation;
the host exchange remains visible in the open game. This is a periodic
witness, not a general recursion denotation or a completeness result.

```sh
make check CHECK_TARGETS='+Silmaril.Wasm.Game.Intrinsic.Requests.Repeat.Example'
```
