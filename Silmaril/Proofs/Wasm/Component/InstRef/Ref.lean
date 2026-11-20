module

public import Silmaril.Wasm.Component.InstRef.Defs
public import Silmaril.Proofs.Wasm.Component.Reference.LitmusImp
public import Silmaril.Proofs.Wasm.Component.Reference.LitmusRef
public import Silmaril.Proofs.Wasm.Component.Reference.LinkedSession.Main

/-!
# Start functions on the reference machine: litmus runs

Runs of the reference machine, computed by kernel evaluation of its executable drivers
(`decide +kernel`) and turned into behaviours by the drivers' soundness theorems:

* `callSI_ref`: instantiating `callSI` under the logging host succeeds, and the log of host calls
  is `[f(1) ↦ ()]` (`LinkedSession.sessSummary`, `sessSummary_sound`);
* `globSI_ref`: after instantiating `globSI`, `get()` returns `42` (`callSummaryI`,
  `returns_of_summaryI`);
* `trapSI_ref`: instantiating `trapSI` traps (`trapSummary`, `traps_of_summary`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.InstRef

open Silmaril.Games Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.InstRef Silmaril.Wasm.Component.InstLitmus
open Silmaril.Proofs.Wasm.Component.Reference.Litmus
open Silmaril.Wasm.Component.Reference.Core3Adder (first)

theorem callSI_summary' :
    (LinkedSession.sessSummary embL first 400 callSI.toRef callSI.imports ((), []) []).map
      (fun p => (p.1, p.2.2)) = some ([], [(⟨0⟩, [toRefVal (.u32 1)], [])]) := by
  decide +kernel

theorem callSI_summary :
    LinkedSession.sessSummary embL first 400 callSI.toRef callSI.imports ((), []) [] =
      some ([], ((), [(⟨0⟩, [toRefVal (.u32 1)], [])])) := by
  obtain ⟨⟨outs, u, log⟩, h, he⟩ := Option.map_eq_some_iff.1 callSI_summary'
  cases u
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  exact h

theorem callSI_ref :
    (([] : List (Option (List Value.Val))), ((), [((⟨0⟩ : Runtime.HostFuncId),
      [toRefVal (.u32 1)], ([] : List Value.Val))])) ∈
      LinkedSession.sessRunBehaviours first.prof (Host.ofEmbedder embL) ((), []) callSI.toRef
        callSI.imports [] :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedSession.sessSummary_sound callSI_summary

theorem globSI_ref : Outcome.returns (some [toRefVal (.u32 42)]) ∈
    exportBehavioursI first.prof (Host.ofEmbedder Silmaril.Wasm.Component.Reference.Litmus.embI) () globSI.toRef globSI.imports "get" [] :=
  returns_of_summaryI (by decide +kernel)

section Trap

open Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.Canon

/-- The instantiation of `c` with no arguments from the empty store traps without an `internal`
fault, within `fuel` steps of `embT` (which executes core code). -/
def trapSummaryT (fuel : Nat) (c : Core3Component) : Bool :=
  match hostStep? embT.hr (instantiateTop c []) (initConfig ()) with
  | none => false
  | some (_, m₁) =>
    let r := Machine.run embT.hr embT.dispatch embT.X first fuel m₁
    decide (r.outcome = .trap) && !(r.labels.any Label.isInternalTrap)

/-- A trapping summary is a trapping instantiation of the reference machine. -/
theorem traps_of_summaryT {fuel : Nat} {c : Core3Component} (h : trapSummaryT fuel c = true) :
    InstResult.traps ∈ instBehaviours first.prof (Host.ofEmbedder embT) (initConfig ()) c [] := by
  unfold trapSummaryT at h
  split at h
  next => cases h
  next l m₁ e =>
    have ho : (Machine.run embT.hr embT.dispatch embT.X first fuel m₁).outcome = .trap ∧
        (Machine.run embT.hr embT.dispatch embT.X first fuel m₁).labels.any
          Label.isInternalTrap = false := by
      simpa only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_eq_eq_not, Bool.not_true]
        using h
    have hl : l = .host (instantiateTop c []) := hostStep?_run_label e
    have s₁ := hostStep?_sound first.prof embT.hr embT.dispatch e
    have hs := Machine.run_sound embT.hr embT.dispatch embT.X first fuel m₁
    have hT : Trapped (Machine.run embT.hr embT.dispatch embT.X first fuel m₁).config := by
      rcases Machine.run_outcome embT.hr embT.dispatch embT.X first fuel m₁ with e' | e'
      · exact absurd (e'.symm.trans ho.1) (by decide)
      · exact outcomeOf_trap _ (e' ▸ ho.1)
    refine ⟨_, _, hl ▸ Steps.cons s₁ hs, run_noHost _ _ _ _ _ _, fun msg hm => ?_, hT⟩
    have hany : (Machine.run embT.hr embT.dispatch embT.X first fuel m₁).labels.any
        Label.isInternalTrap = true :=
      List.any_eq_true.mpr ⟨_, hm, Label.isInternalTrap_trap_internal msg⟩
    exact absurd (hany.symm.trans ho.2) (by decide)

end Trap

theorem trapSI_ref : InstResult.traps ∈ instBehaviours first.prof (Host.ofEmbedder embT)
    (initConfig ()) trapSI.toRef [] :=
  traps_of_summaryT (fuel := 200) (by decide +kernel)

end Silmaril.Proofs.Wasm.Component.InstRef
