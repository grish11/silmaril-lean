module

public import Silmaril.Wasm.Component.InstLitmus.Defs
public import Silmaril.Wasm.Component.InstSem.Thms
public import Silmaril.Wasm.SingleThreaded.Interface
import Silmaril.Proofs.Wasm.Component.InstLitmus.Neg
import Silmaril.Proofs.Wasm.Component.InstLitmus.Export
public import Silmaril.Wasm.Component.InstExport.Defs

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

**The export phase** (proofs in `Silmaril.Proofs.Wasm.Component.InstLitmus.Export`; `getQ` is
`get()`, `a42` the answer `42`):

* (e) `globC_get` (every profile): `globMod`'s start function writes `42` into a global; after
  `[inst, ready]` the exported `get()` is answered `42`; `globC_denX_get`: the same play in the
  export phase `Comp.denX`;
* (e) `globMod_get_det` (deterministic profiles, the module alone): after a successful
  instantiation `get()` is answered `42` **only** (by the converse
  `Param.core3_after_start_iff` and the uniqueness of normal forms);
* (f) `callGlobC_get` (every profile): `callMod 1`'s start function calls `f(1)`, then
  `globMod`'s start function runs, then the instantiation is ready and the exported `get()`
  is answered `42`;
* (g) `trap1C_inst_fails` (every profile): a trapping start function fails the
  instantiation; `trapC_denX` (deterministic profiles): the export phase of `trapC` is `⊥`, it
  never answers an export call.

Not shown: the deterministic-profile *component-level* uniqueness of the export answers of
`globC` and `callGlobC` (only the module-level `globMod_get_det` is proved), and the
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

/-! ## The export phase -/

/-- **(e) A start function's write is seen by the export**: after `[inst, ready]`, `get()` is
answered `42`. -/
theorem globC_get (P : Profile) :
    ([askInst, ansInst .ready, askEx getQ, ansEx getQ a42] : List (Move sigU sigUI)) ∈
      globC.denI (core3SemI P) :=
  Silmaril.Proofs.Wasm.Component.InstLitmus.globC_play P

/-- **(e) In the export phase of `globC`, `get()` is answered `42`.** -/
theorem globC_denX_get (P : Profile) :
    ([.inr (.ask getQ), .inr (.ans getQ a42)] : List (Move sigU sigU)) ∈
      globC.denX (core3SemI P) :=
  Strategy.subset_generate ⟨[], globC_get P⟩ ⟨_, .cons (.ask _) (.cons (.ret _ _) (.nil _))⟩

/-- **(e) Only `42`, at a deterministic profile**: after a successful instantiation of `globMod`,
`get()` is answered `42` and nothing else. -/
theorem globMod_get_det (o : GrowOracle) {cs : List (Σ _ : (sigN 0).Op, Option Payload)}
    {r : Option Payload}
    (h : instPlay (F := sigN 1) cs .ready ++ ([askEx getM, ansEx getM r] :
      List (Move (sigN 0) ((sigN 1).withInst Unit))) ∈ (core3SemI (profile o)).sem globMod) :
    r = a42 :=
  Silmaril.Proofs.Wasm.Component.InstLitmus.globMod_get_det (o := o) h

/-- **(f) Two start functions in order, then the export**: `callMod 1`'s start function calls
`f(1)`, `globMod`'s writes `42`, the instantiation is ready, and `get()` is answered `42`. -/
theorem callGlobC_get (P : Profile) :
    ([askInst, .inl (.ask (fQ 1)), .inl (.ans (fQ 1) unitA), ansInst .ready, askEx getQ,
      ansEx getQ a42] : List (Move sigU sigUI)) ∈ callGlobC.denI (core3SemI P) :=
  Silmaril.Proofs.Wasm.Component.InstLitmus.callGlobC_play P

/-- **(g) A trapping start function fails the instantiation of `trap1C`.** -/
theorem trap1C_inst_fails (P : Profile) :
    ([askInst, ansInst (.fail ())] : List (Move sigU sigUI)) ∈ trap1C.denI (core3SemI P) :=
  Silmaril.Proofs.Wasm.Component.InstLitmus.trap1C_inst P

/-- **(c) After a start trap, no export is ever answered**: the export phase of `trapC` is `⊥`,
at a deterministic profile. -/
theorem trapC_denX (o : GrowOracle) : trapC.denX (core3SemI (profile o)) = ⊥ :=
  Silmaril.Proofs.Wasm.Component.InstLitmus.trapC_denX

end Silmaril.Wasm.Component.InstLitmus
