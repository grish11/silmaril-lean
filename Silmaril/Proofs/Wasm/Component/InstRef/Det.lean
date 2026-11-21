module

public import Silmaril.Proofs.Wasm.Component.InstRef.IR
public import Silmaril.Proofs.Wasm.Component.InstLitmus.Det

/-!
# The reference litmus components at a deterministic profile

Bounded by scripts (`Silmaril.Proofs.Wasm.Component.InstLitmus.Det`):

* `callSI_asks`: the host calls of every play of `callSI.toComp` are a prefix of `[f(u32 1)]`;
* `trapSI_plays`: every play of `trapSI.toComp` is a prefix of `[inst, fail ()]`, possibly
  followed by one Opponent move; its export phase never answers (`trapSI_denX`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.InstRef

open Silmaril.Games Silmaril.Games.Inst Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.Param Silmaril.Wasm.Component.InstLitmus
open Silmaril.Wasm.Component.InstRef
open Silmaril.Proofs.Wasm.Component.InstSem Silmaril.Proofs.Wasm.Component.InstEngine
open Silmaril.Proofs.Wasm.Component.InstLitmus
open Silmaril.Wasm.Game (liftMove)
open Silmaril.Wasm.SingleThreaded (GrowOracle profile)

variable {o : GrowOracle}

/-- The script of `callSI.toComp`. -/
def callSIH : Handler sigU sigUI :=
  (extScriptH 1 (baseH 1)
    ((implsN 1 (SimpleI.lowerArgs hostI) 1).comp ((callS 1).comp (liftH (widenH 0))))).comp
    (liftH (exportsH 1 []))

/-- The script of `trapSI.toComp`. -/
def trapSIH : Handler sigU sigUI :=
  (extScriptH 0 (baseH 0) ((implsN 0 [] 0).comp (trapS.comp (liftH (widenH 1))))).comp
    (liftH (exportsH 1 trapSI.toComp.exports))

theorem callSI_le : callSI.toComp.denIR (core3SemI (profile o)) ≤ Strategy.ofHandler callSIH := by
  rw [SimpleI.toComp, Comp.denIR]
  simp only [denNodesI, Node.denI]
  rw [callSIH, Strategy.ofHandler_comp, base_eq]
  refine Strategy.comp_mono ?_ le_rfl
  rw [← extI_ofHandler]
  exact extI_mono _ le_rfl (coreNodeI_le (callMod_le_script callPrep_one) _ _)

theorem trapSI_le : trapSI.toComp.denIR (core3SemI (profile o)) ≤ Strategy.ofHandler trapSIH := by
  rw [SimpleI.toComp, Comp.denIR]
  simp only [denNodesI, Node.denI]
  rw [trapSIH, Strategy.ofHandler_comp, base_eq]
  refine Strategy.comp_mono ?_ le_rfl
  rw [← extI_ofHandler]
  exact extI_mono _ le_rfl (coreNodeI_le trapMod_le_script _ _)

theorem trapSIH_inst : trapSIH none = .pure (.fail ()) := rfl

theorem callSIH_inst : Prog.AsksWithin (callSIH none) [fV] := by
  refine .call fun r₁ => ?_
  rcases r₁ with _ | ((_ | ⟨x, xs⟩) | (_ | ⟨v, vs⟩))
  all_goals exact .pure _ _

theorem callSIH_ex (q : sigU.Op) : callSIH (some q) = .pure none := rfl

/-- **The host calls of every play of `callSI.toComp` are a prefix of `[f(u32 1)]`.** -/
theorem callSI_asks {p : List (Move sigU sigUI)}
    (hp : p ∈ callSI.toComp.denI (core3SemI (profile o))) : lowerAsks p <+: [fV] := by
  obtain ⟨q, hq, hpr, hpq⟩ := guard_plays callSI_le hp
  have h := handler_proper_asks callSIH_inst (fun q => ⟨none, callSIH_ex q⟩) hq hpr
  rcases hpq with h' | ⟨q₀, x, rfl, h', hx⟩
  · exact (lowerAsks_prefix h').trans h
  · rw [lowerAsks_append, lowerAsks_isO hx, List.append_nil]
    exact (lowerAsks_prefix h').trans h

/-- **Every play of `trapSI.toComp` is a prefix of `[inst, fail ()]`**, possibly followed by one
Opponent move. -/
theorem trapSI_plays {p : List (Move sigU sigUI)}
    (hp : p ∈ trapSI.toComp.denI (core3SemI (profile o))) :
    p <+: [askInst, ansInst (.fail ())] ∨
      ∃ q₀ x, p = q₀ ++ [x] ∧ q₀ <+: [askInst, ansInst (.fail ())] ∧ x.IsO := by
  obtain ⟨q, hq, hpr, hpq⟩ := guard_plays trapSI_le hp
  have h := handler_proper_fail trapSIH_inst hq hpr
  rcases hpq with h' | ⟨q₀, x, rfl, h', hx⟩
  · exact .inl (h'.trans h)
  · exact .inr ⟨q₀, x, rfl, h'.trans h, hx⟩

/-- **The export phase of `trapSI.toComp` never answers.** -/
theorem trapSI_denX : trapSI.toComp.denX (core3SemI (profile o)) = ⊥ := by
  rw [Strategy.bot_eq_generate, Comp.denX, exportPhase]
  congr 1
  ext p
  simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists]
  intro cs h
  have hr : ansInst .ready ∈ instPlay (F := sigU) cs (InstAns.ready (R := Unit)) ++
      p.map liftMove := by simp [instPlay]
  have hsub : ∀ {q : List (Move sigU sigUI)}, q <+: [askInst, ansInst (.fail ())] →
      ansInst .ready ∉ q := by
    intro q hq hm
    have := hq.subset hm
    simp [ansInst, askInst] at this
    cases this
  rcases trapSI_plays h with h' | ⟨q₀, x, he, h', hx⟩
  · exact hsub h' hr
  · rw [he] at hr
    rcases List.mem_append.1 hr with hr | hr
    · exact hsub h' hr
    · rw [List.mem_singleton] at hr
      subst hr
      exact hx

end Silmaril.Proofs.Wasm.Component.InstRef
