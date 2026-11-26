# Weaken a guarded SCCP entry with an unused capture

`TwoBackedges.Weakening.program` prepends one fresh value sort to the
typed register bank of the fixed pure five-block loop. The existing
`Port.tail` embeds every old read, write, and terminator port. This
includes operands in both feedback routes. `project` drops the fresh
coordinate. `block_eval` proves the fresh value survives each block
unchanged, and `source_run` preserves the native return or exhaustion
at each source block budget.
[Native weakening](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/TwoBackedges/Weakening/Thms.lean)

`facts` prepends an overdefined fact, so every typed fresh value is
allowed. `transfer_project` commutes with the existing SCCP equations.
`solve_project` uses leastness to preserve all old facts, the exact
result fact, and each occurrence mark. Consequently `Guarded.replay`
runs the existing FIFO checker and selects the same singleton feedback
route. `Guarded.compile` replays admission and invokes the existing
guarded emitters. `compile_eq` identifies its actual result with
emission from the transported certificate.
[Checker and emitters](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/TwoBackedges/Weakening/Guarded/Defs.lean)

`cf_guard` and `numbered_guard` prove that both emitted entry tests
choose the original arm on the projected valuation. The emitted graphs
can forward the fresh value through their typed bank packets. The value
has no source operand uses or coverage tests. `backend_returns`
compares exact words using independent witnesses, and `backend_noReturn`
compares absence of finite observation. CF uses block runs, numbered
RVSDG uses θ runs, and linked coloured Petri uses existence of a finite
completed trace.

The native and generated corridors translate equations and termination
sentences forward and reduce valuations by projection.
`emit_commutes` compares re-emission along the two paths. It is a local
square between the existing rooms at the two signatures. The signature
arrows in [the permutation institution](rice-loop-sccp-guarded-institution.md)
still use typed bijections. This weakening fixes the primitive
interpretation, return width, and five-block profile.
[Guard, return and satisfaction laws](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/TwoBackedges/Weakening/Guarded/Thms.lean)

## Replay and run with two fresh values

The executable fixture prepends an unused `i16` to the original
`[again, select, byte]` bank. The triples report the native, CF, and
numbered result using their own bounds. The outer option reports replay
admission.

```lean
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Weakening.Guarded.Example.Defs

open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Weakening.Guarded.Example
  (checkedSide run)

#eval checkedSide
-- some true

#eval (run 0 true, run 65535 true)
-- (some (some 99, some 99, some 99), some (some 99, some 99, some 99))

#eval (run 0 false, run 65535 false)
-- (some (some 7, some 7, some 7), some (some 7, some 7, some 7))
```

The checked regression also instantiates the finite-return law and proves
absence of a finite observation for an admitted looping program at every
fresh value.
[Regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Quads/Loop/Tail/TwoBackedges/Weakening/Guarded/Regression.lean)
