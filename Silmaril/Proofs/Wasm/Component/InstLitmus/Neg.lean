module

public import Silmaril.Proofs.Wasm.Component.InstLitmus.Det

/-!
# Instantiation litmus components at a deterministic profile: what cannot happen

The litmus components are bounded by the scripts of their modules (`Det`), so by handlers
(`extI_ofHandler`, `Strategy.ofHandler_comp`): `trapC_le`, `twoC_le`. The handlers' programs
for `inst` are computed by reduction: `trapC`'s fails at once, `twoC`'s calls `f(1)` and then,
if the answer is `()`, `f(2)`. Under the protocol guard the plays of `Comp.denI` follow these
programs (`guard_plays`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.InstLitmus

open Silmaril.Games Silmaril.Games.Inst Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.Param Silmaril.Wasm.Component.InstLitmus
open Silmaril.Proofs.Wasm.Component.InstSem Silmaril.Proofs.Wasm.Component.InstEngine
open Silmaril.Wasm.SingleThreaded (GrowOracle profile)

variable {o : GrowOracle}

/-! ## Bounds by handlers -/

theorem coreNodeI_le {C : CoreSemI ImpModule} {m : ImpModule}
    {S : Handler (CoreIface.sig (CoreModule.imports m))
      ((CoreIface.sig (CoreModule.exports m)).withInst Unit)}
    (h : C.sem m ≤ Strategy.ofHandler S) (e : Nat) (args : List Impl) :
    coreNodeI C e m args ≤ Strategy.ofHandler ((implsN e args (CoreModule.imports m).length).comp
      (S.comp (liftH (widenH (CoreModule.exports m).length)))) := by
  rw [Strategy.ofHandler_comp, Strategy.ofHandler_comp]
  exact Strategy.comp_mono le_rfl (Strategy.comp_mono h le_rfl)

theorem base_eq (n : Nat) :
    withReady (R := Unit) (Strategy.ofHandler (maskH n)) =
      Strategy.ofHandler ((maskH n).comp (readyH sigU Unit)) := by
  rw [withReady, Strategy.ofHandler_comp]

/-- The script of the imports. -/
abbrev baseH (n : Nat) : Handler sigU sigUI := (maskH n).comp (readyH sigU Unit)

/-- The script of `trapC`. -/
def trapCH : Handler sigU sigUI :=
  (extScriptH 2 (extScriptH 1 (baseH 1) ((implsN 1 [] 0).comp (trapS.comp (liftH (widenH 1)))))
    ((implsN 2 [Impl.fwd 0] 1).comp ((callS 2).comp (liftH (widenH 0))))).comp
    (liftH (exportsH 2 [getX 1]))

/-- The script of `twoC`. -/
def twoCH : Handler sigU sigUI :=
  (extScriptH 1 (extScriptH 1 (baseH 1)
      ((implsN 1 [Impl.fwd 0] 1).comp ((callS 1).comp (liftH (widenH 0)))))
    ((implsN 1 [Impl.fwd 0] 1).comp ((callS 2).comp (liftH (widenH 0))))).comp
    (liftH (exportsH 1 []))

theorem trapC_le : trapC.denIR (core3SemI (profile o)) ≤ Strategy.ofHandler trapCH := by
  rw [trapC, Comp.denIR]
  simp only [denNodesI, Node.denI]
  rw [trapCH, Strategy.ofHandler_comp, base_eq]
  refine Strategy.comp_mono ?_ le_rfl
  rw [← extI_ofHandler, ← extI_ofHandler]
  exact extI_mono _ (extI_mono _ le_rfl (coreNodeI_le trapMod_le_script _ _))
    (coreNodeI_le (callMod_le_script callPrep_two) _ _)

theorem twoC_le : twoC.denIR (core3SemI (profile o)) ≤ Strategy.ofHandler twoCH := by
  rw [twoC, Comp.denIR]
  simp only [denNodesI, Node.denI]
  rw [twoCH, Strategy.ofHandler_comp, base_eq]
  refine Strategy.comp_mono ?_ le_rfl
  rw [← extI_ofHandler, ← extI_ofHandler]
  exact extI_mono _ (extI_mono _ le_rfl (coreNodeI_le (callMod_le_script callPrep_one) _ _))
    (coreNodeI_le (callMod_le_script callPrep_two) _ _)

/-! ## The programs for `inst` -/

theorem trapCH_inst : trapCH none = .pure (.fail ()) := rfl

theorem twoCH_inst : Prog.AsksWithin (twoCH none) [fQ 1, fQ 2] := by
  refine .call fun r₁ => ?_
  rcases r₁ with _ | ((_ | ⟨x, xs⟩) | vs)
  · exact .pure _ _
  · refine .call fun r₂ => ?_
    rcases r₂ with _ | ((_ | ⟨y, ys⟩) | vs')
    all_goals exact .pure _ _
  · exact .pure _ _
  · exact .pure _ _

theorem twoCH_ex (q : sigU.Op) : twoCH (some q) = .pure none := rfl

/-! ## The plays -/

/-- **(c)** Every play of `trapC` is a prefix of `[inst, fail ()]`, possibly followed by one
Opponent move that is never answered. -/
theorem trapC_plays {p : List (Move sigU sigUI)} (hp : p ∈ trapC.denI (core3SemI (profile o))) :
    p <+: [askInst, ansInst (.fail ())] ∨
      ∃ q₀ x, p = q₀ ++ [x] ∧ q₀ <+: [askInst, ansInst (.fail ())] ∧ x.IsO := by
  obtain ⟨q, hq, hpr, hpq⟩ := guard_plays trapC_le hp
  have h := handler_proper_fail trapCH_inst hq hpr
  rcases hpq with h' | ⟨q₀, x, rfl, h', hx⟩
  · exact .inl (h'.trans h)
  · exact .inr ⟨q₀, x, rfl, h'.trans h, hx⟩

theorem trapC_moves {p : List (Move sigU sigUI)} (hp : p ∈ trapC.denI (core3SemI (profile o))) :
    ∀ y ∈ p, y = askInst ∨ y = ansInst (.fail ()) ∨ y.IsO := by
  have hsub : ∀ {q : List (Move sigU sigUI)}, q <+: [askInst, ansInst (.fail ())] →
      ∀ y ∈ q, y = askInst ∨ y = ansInst (.fail ()) := by
    intro q hq y hy
    have := hq.subset hy
    simpa using this
  rcases trapC_plays hp with h | ⟨q₀, x, rfl, h, hx⟩
  · intro y hy
    rcases hsub h y hy with h | h
    · exact .inl h
    · exact .inr (.inl h)
  · intro y hy
    rcases List.mem_append.1 hy with hy | hy
    · rcases hsub h y hy with h | h
      · exact .inl h
      · exact .inr (.inl h)
    · rw [List.mem_singleton.1 hy]; exact .inr (.inr hx)

/-- **(a)** The host calls of every play of `twoC` are, in order, a prefix of `f(1), f(2)`. -/
theorem twoC_order {p : List (Move sigU sigUI)} (hp : p ∈ twoC.denI (core3SemI (profile o))) :
    lowerAsks p <+: [fQ 1, fQ 2] := by
  obtain ⟨q, hq, hpr, hpq⟩ := guard_plays twoC_le hp
  have h := handler_proper_asks twoCH_inst (fun q => ⟨none, twoCH_ex q⟩) hq hpr
  rcases hpq with h' | ⟨q₀, x, rfl, h', hx⟩
  · exact (lowerAsks_prefix h').trans h
  · rw [lowerAsks_append, lowerAsks_isO hx, List.append_nil]
    exact (lowerAsks_prefix h').trans h

end Silmaril.Proofs.Wasm.Component.InstLitmus
