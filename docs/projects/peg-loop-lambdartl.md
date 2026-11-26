# Checked PEG loops to cyclic λRTL

[LambdaRTL.Defs](../../Silmaril/SSA/PEG/Bridge/Theta/Region/LambdaRTL/Defs.lean)
lowers the checked ordered PEG loop bundle to a named, mutable
`Silmaril.SSA.LambdaRTL.CFG`. The input is the same pure single-loop
certificate used for numbered RVSDG θ, with a shared pass for all eval
roots, ordered typed carried slots, and straight-line guard and update
schedules. It supports finite heterogeneous tuples whose arity and sorts
stay fixed across the loop.

Each block takes one packet. The representation reuses the tagged atoms,
primitive profiles and right-nested pair/unit encoding from the
[loop-free bridge](../../Silmaril/SSA/PEG/Bridge/ForwardCFG/Defs.lean).
Pair elimination loads the old slots into disjoint registers. Each
certified primitive becomes a native λRTL `let1` into a fresh temporary with
its ordered, tagged operands. The before block tests the positive guard
using a Boolean-to-sum instruction and an ordinary λRTL case terminator.
True jumps to the after block with the old tuple. After executes the
update schedule and packs the next tuple before jumping back to before.
All reads of old carried values therefore see the same snapshot. False
branches directly to the absent exit label with the old tuple. An
initially false guard executes no update instructions.

[LambdaRTL.Thms](../../Silmaril/SSA/PEG/Bridge/Theta/Region/LambdaRTL/Thms.lean)
proves the finite-return correspondence against
[`CFG.Cyclic.run`](../../Silmaril/SSA/LambdaRTL/CFG/Cyclic/Defs.lean).
The executable budget runner calls the same full-table mutable-store
`step`. [`mem_run_iff_runFuel`](../../Silmaril/SSA/LambdaRTL/CFG/Cyclic/Fuel/Thms.lean)
relates existence of a budget to membership in the `Part` semantics,
including the final store.

- `observeFuel_eq` relates a budget of `f` target steps to
  `f / 2` numbered θ activations. A continuing activation spends one
  step on each block. A stopping activation spends one step on before
  and one resolving the absent exit label. The entry branch is free
  under this budget convention.
- `observe_result` and `returns_iff_numbered` give the exact exit and
  packed result of finite λRTL execution. The observation projects
  away the final scratch store.
- `returns_iff_observe` composes this result with the checked bundle's
  Figure 11 theorem. Under the total primitive interpretation and the
  premise that the marked PEG negation computes Boolean complement,
  a finite λRTL run returns the packed ordered tuple iff the PEG
  observation is that same fully defined tuple. `firstExit_of_return`
  recovers the shared first pass and defined eval prefixes.

The target syntax is λRTL with explicit typed primitive profiles and a
tag-checked packet boundary. Its atoms can carry arbitrary model data,
and its pair and sum values are semantic constructors. Counts are natural
numbers, Booleans use the PEG Boolean sort, and data sorts use the
chosen total model carriers. The machine
RTL [carried-bank lowering](../../Silmaril/Machine/SeaOfNodes/Loop/RTL/CarriedBank/Thms.lean)
uses a specific word-level graph and calling convention. A connection
there would require a representable word profile and a verified
primitive and packet-to-register calling convention. The proof here
concerns finite successful returns for the compiler image. Partial
primitives, traps, effects and observable divergence are outside
this result.

The [regression](../../tests/ssa/PEGStructuredTheta.lean) checks the
emitted operations and backedge. Two updates transform `(2, 10, 1)`
through `(1, 1, 11)` to `(0, 11, 12)`. An initially zero counter
returns `(0, 10, 1)` and leaves the update-only temporary untouched.
The test also instantiates both directions of the Figure 11 theorem.

```sh
lake build --wfail PEGStructuredThetaTests PEGForwardCFGTests
```
