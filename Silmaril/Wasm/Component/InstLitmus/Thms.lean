module

public import Silmaril.Wasm.Component.InstLitmus.Defs
public import Silmaril.Wasm.Component.InstSem.Thms
public import Silmaril.Wasm.SingleThreaded.Interface
import Silmaril.Proofs.Wasm.Component.InstLitmus.Neg

/-!
# Instantiation litmus components: theorems

All proved, over the Core 3.0 engine with an instantiation phase (`Param.core3SemI`); proofs in
`Silmaril.Proofs.Wasm.Component.InstLitmus`. The instances are computed by kernel evaluation
(`decide +kernel` on Boolean summaries of `prepareE?`); the start runs are Core 3.0 runs built
from `Step` rules. Plays are over `sigU ↠ sigUI`: `askInst`/`ansInst a` are the instantiation
question and its answer, `.inl` moves are calls of the host import `f` (`fQ k` is `f(k)`,
`unitA` the answer `()`).

**At every profile `P`** (instantiation plays exist):

* (a) `twoC_inst`: instantiating `twoC` runs the start function of the first instance, which
  calls `f(1)`, then that of the second, which calls `f(2)`, then is ready;
* (b) `oneC_inst`: a start function's import call is a move of the instantiation;
* (c) `trapC_inst_fails`: the first instance's start function traps, and the instantiation
  fails at once (`[inst, fail ()]`);
* (d) `hiddenC_inst`: the start function of an instance that has no exports and that nothing
  calls runs at instantiation: its call `f(1)` is in the instantiation play.

**At every deterministic profile `profile o`** (what cannot happen; the modules are bounded by
scripts, so the components by handlers):

* (a) `twoC_order`: in every play of `twoC`, the host calls are a prefix of `f(1), f(2)`: the
  second start function never calls before the first;
* (c) `trapC_plays`: every play of `trapC` is a prefix of `[inst, fail ()]`, possibly followed
  by one Opponent move that is never answered; hence `trapC_not_ready` (instantiation never
  succeeds), `trapC_no_host_calls` (no host call happens: the second instance's start function
  `f(2)` never runs) and `trapC_no_exports` (the exported `get` is never answered).

Not shown: plays of the export phase after instantiation for these components, and the
deterministic-profile statements at other profiles (they use the uniqueness of normal forms of
Core 3.0 runs, `Silmaril.Wasm.Game.reach_normal_unique`).
-/

public section

namespace Silmaril.Wasm.Component.InstLitmus

open Silmaril.Games Silmaril.Games.Inst Silmaril.Wasm.Component Silmaril.Wasm.Component.Param
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.SingleThreaded (GrowOracle profile)

/-- **(a) Instances are instantiated in program order**: the start function of the first
instance calls `f(1)`, then that of the second calls `f(2)`. -/
theorem twoC_inst (P : Profile) :
    ([askInst, .inl (.ask (fQ 1)), .inl (.ans (fQ 1) unitA), .inl (.ask (fQ 2)),
      .inl (.ans (fQ 2) unitA), ansInst .ready] : List (Move sigU sigUI)) ∈
      twoC.denI (core3SemI P) :=
  Silmaril.Proofs.Wasm.Component.InstLitmus.twoC_inst P

/-- **(a) Order, at a deterministic profile**: the host calls of every play are a prefix of
`f(1), f(2)`. -/
theorem twoC_order (o : GrowOracle) {p : List (Move sigU sigUI)}
    (hp : p ∈ twoC.denI (core3SemI (profile o))) : lowerAsks p <+: [fQ 1, fQ 2] :=
  Silmaril.Proofs.Wasm.Component.InstLitmus.twoC_order hp

/-- **(b) A start function's import call is a move of the instantiation.** -/
theorem oneC_inst (P : Profile) :
    ([askInst, .inl (.ask (fQ 1)), .inl (.ans (fQ 1) unitA), ansInst .ready] :
      List (Move sigU sigUI)) ∈ oneC.denI (core3SemI P) :=
  Silmaril.Proofs.Wasm.Component.InstLitmus.oneC_inst P

/-- **(c) A trapping start function fails the instantiation.** -/
theorem trapC_inst_fails (P : Profile) :
    ([askInst, ansInst (.fail ())] : List (Move sigU sigUI)) ∈ trapC.denI (core3SemI P) :=
  Silmaril.Proofs.Wasm.Component.InstLitmus.trapC_inst P

/-- **(c) The plays of `trapC`, at a deterministic profile**: a prefix of `[inst, fail ()]`,
possibly followed by one Opponent move that is never answered. -/
theorem trapC_plays (o : GrowOracle) {p : List (Move sigU sigUI)}
    (hp : p ∈ trapC.denI (core3SemI (profile o))) :
    p <+: [askInst, ansInst (.fail ())] ∨
      ∃ q₀ x, p = q₀ ++ [x] ∧ q₀ <+: [askInst, ansInst (.fail ())] ∧ x.IsO :=
  Silmaril.Proofs.Wasm.Component.InstLitmus.trapC_plays hp

/-- **(c) The instantiation of `trapC` never succeeds.** -/
theorem trapC_not_ready (o : GrowOracle) {p : List (Move sigU sigUI)}
    (hp : p ∈ trapC.denI (core3SemI (profile o))) : ansInst .ready ∉ p := by
  intro h
  rcases Silmaril.Proofs.Wasm.Component.InstLitmus.trapC_moves hp _ h with h | h | h
  · cases h
  · cases h
  · exact h

/-- **(c) No host call happens in `trapC`**: in particular the second instance's start function
never calls `f(2)`. -/
theorem trapC_no_host_calls (o : GrowOracle) {p : List (Move sigU sigUI)}
    (hp : p ∈ trapC.denI (core3SemI (profile o))) (m : sigU.Op) : .inl (.ask m) ∉ p := by
  intro h
  rcases Silmaril.Proofs.Wasm.Component.InstLitmus.trapC_moves hp _ h with h | h | h
  · cases h
  · cases h
  · exact h

/-- **(c) The exports of `trapC` are never answered.** -/
theorem trapC_no_exports (o : GrowOracle) {p : List (Move sigU sigUI)}
    (hp : p ∈ trapC.denI (core3SemI (profile o))) (q : sigU.Op) (r : Option Payload) :
    ansEx q r ∉ p := by
  intro h
  rcases Silmaril.Proofs.Wasm.Component.InstLitmus.trapC_moves hp _ h with h | h | h
  · cases h
  · cases h
  · exact h

/-- **(d) An instance that has no exports and that nothing calls is still instantiated**: its
start function's call `f(1)` is in the instantiation play. -/
theorem hiddenC_inst (P : Profile) :
    ([askInst, .inl (.ask (fQ 1)), .inl (.ans (fQ 1) unitA), ansInst .ready] :
      List (Move sigU sigUI)) ∈ hiddenC.denI (core3SemI P) :=
  Silmaril.Proofs.Wasm.Component.InstLitmus.hiddenC_inst P

end Silmaril.Wasm.Component.InstLitmus
