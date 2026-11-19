module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeResEdge
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.CallIndGoodRun
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.GoodMergeLoad

/-!
# The 2.0 whole-step bridge: the last open backward target, and packed loads under contexts

* **`not_wholeStepBwd`**: `Sim20.Task.wholeStepBwd`, the backward half with the builtins chosen
  existentially and no hypothesis beyond a typed image, is false. `Step/memory.grow-fail` has no
  premise, so it fires at `i32.const 0; memory.grow` in a frame without a memory at *every*
  builtins (`fires20_memGrowFail`), where V2 has no step (`not_step_memGrow`). This strengthens
  `not_wholeStepBwd_noRes`, which fixes the builtins to `floatIntB`. The surviving backward
  statement is `Task.wholeStepBwdW` (proved), whose `ResOkL` excludes this configuration.
* **`fwdBase20_fwdGP`**, **`Task.wholeStepFwd20GP`** (proved, `wholeStepFwd20GP`): the widest
  nested forward fragment in the corrected script `simEnv20S (storeB P)`, `FwdStep20G`, joined
  with V2's packed loads (`load-pack-trap`, `load-pack-val`, `GoodMerge.LoadPackFwd20`) by the
  generic union `FwdBase20.or` and closed under the three evaluation contexts by `fwd_nest20`.
  Before this, packed loads were nested only in the `STORE`-erratum script `simEnv20T`
  (`GoodMerge.fwd_good20M`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.Whole

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (SStepB)
open Silmaril.Wasm.SpecTec.Sim20.StepFix (simEnv20S)

/-! ## The backward half without a resource hypothesis -/

/-- **`Task.wholeStepBwd` is false**, whatever builtins are chosen: `memory.grow-fail` fires
without a memory, where V2 is stuck. -/
theorem not_wholeStepBwd : ¬ Task.wholeStepBwd := by
  intro h
  obtain ⟨B, hB⟩ := h Empty Empty.elim (fun a => a.elim) (fun _ _ _ _ => False) false {}
  obtain ⟨c', -, hs⟩ := hB memGrowCfg _ (typed20_memGrow B) (sstepB_memGrow B)
  exact not_step_memGrow hs rfl (Or.inl ⟨0, rfl⟩)

/-! ## Packed loads under contexts, in the corrected script -/

variable {H : Type} {hn : H → String}

/-- **The widest nested base with packed loads**: `FwdStep20G` or a packed load, at `storeB`. -/
abbrev FwdStep20GP (P : Profile) (c c' : Config H) : Prop :=
  CallIndGood.FwdStep20G P c c' ∨ GoodMerge.LoadPackFwd20 c c'

/-- Every step of the base is a V2 step. -/
theorem FwdStep20GP.step {P : Profile} {host : HostSemantics H} {c c' : Config H}
    (h : FwdStep20GP P c c') : Step P host c c' :=
  h.elim (fun h => h.step) (fun h => h.step)

/-- **The joined base is a forward base** at `storeB`, by `FwdBase20.or`. -/
theorem fwdBase20_fwdGP (P : Profile) :
    FwdBase20 (storeB P) hn WholePages (FwdStep20GP (H := H) P) :=
  (CallIndGood.fwdBase20_fwdG P).or (GoodMerge.fwdBase20_loadPack_storeB P)

/-- **The forward 2.0 half on the nested fragment with packed loads** (stated and proved): at
`storeB`, every step of `Nest20 (FwdStep20GP P)` from a configuration with typed image and whole
pages is a step of the corrected script between the images, with a typed successor image. -/
def Task.wholeStepFwd20GP : Prop :=
  ∀ (H : Type) (hn : H → String) (P : Profile) (c c' : Config H),
    Typed20 (simEnv20 (storeB P)) hn c → WholePages c.store → Nest20 (FwdStep20GP P) c c' →
    Typed20 (simEnv20 (storeB P)) hn c' ∧
      SStepB (simEnv20S (storeB P)) (configV hn c) (configV hn c')

/-- **`Task.wholeStepFwd20GP` holds**, at every profile. -/
theorem wholeStepFwd20GP : Task.wholeStepFwd20GP :=
  fun _ _ P _ _ hc hw h => fwd_nest20 (fwdBase20_fwdGP P) h hc hw

/-- **`Task.wholeStepFwd20S`'s fragment is inside the new one**: `FwdStep20L` steps are
`FwdStep20G` steps. -/
theorem nest20_fwdGP_of_fwdL {P : Profile} {c c' : Config H}
    (h : Nest20 (FwdStep20L P) c c') : Nest20 (FwdStep20GP P) c c' :=
  h.mono fun _ _ h => Or.inl (.fwd (.fwd (.fwd (.fwd (.fwd (.fwd h))))))

end Silmaril.Wasm.SpecTec.Sim20.Whole
