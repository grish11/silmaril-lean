module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Public.Stores.Defs
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Public.Construction.Thms
import Mathlib.Data.List.OfFn

public section

namespace Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Public.Stores

open Silmaril.Isotope
open Silmaril.Isotope.Bridge.NamedFlat.Entry.Public (Seeded combineStoreVerdicts)
open Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut (observeRaw)
open Silmaril.SSA.LambdaRTL (CFG)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible
open Silmaril.Elgot.ITree (HandledTrace)

theorem combine_eq_some (verdicts : List (Option Bool)) (verdict : Bool) :
    combineStoreVerdicts verdicts = some verdict ↔
      (∀ result ∈ verdicts, result.isSome = true) ∧
      (verdict = true ↔ ∀ result ∈ verdicts, result = some true) := by
  unfold combineStoreVerdicts
  split
  · rename_i typed
    rw [Option.some.injEq, Bool.eq_iff_iff, List.all_eq_true]
    simp only [beq_iff_eq]
    exact ⟨fun h => ⟨List.all_eq_true.mp typed, h.symm⟩, fun h => h.2.symm⟩
  · rename_i invalid
    simp only [reduceCtorEq, false_iff]
    exact fun h => invalid (List.all_eq_true.mpr h.1)

variable {V K : Type 1} [DecidableEq V] [DecidableEq K] {F : Type} [DecidableEq F]
  {signature : PrimitiveSignature F} {source target : CFG V K F} {exits : List K} {fields : K → List V}
  {leftCapture rightCapture : V} {leftType rightType : PacketType} {outputs : Fin exits.length → PacketType}
  {count : Nat} (left : Seeded signature source exits fields leftCapture leftType outputs)
  (right : Seeded signature target exits fields rightCapture rightType outputs)
  (stores : Fin count → V → Value Atom)

private theorem store_isSome (initial : V → Value Atom) :
    (left.refinementFromStore? right initial).isSome =
      ((left.seed? initial).isSome && (right.seed? initial).isSome) := by
  change ((left.seed? initial).bind fun leftPacket => (right.seed? initial).bind fun rightPacket =>
    some (left.program.refinementBetween? right.program 0 leftPacket 0 rightPacket)).isSome = _
  cases left.seed? initial <;> cases right.seed? initial <;> rfl

private theorem all_typed :
    (List.ofFn fun i => left.refinementFromStore? right (stores i)).all Option.isSome = true ↔
      ∀ i, (left.seed? (stores i)).isSome = true ∧ (right.seed? (stores i)).isSome = true := by
  rw [List.all_eq_true, List.forall_mem_ofFn_iff]
  simp only [store_isSome, Bool.and_eq_true]

theorem eq_none :
    left.refinementOverStores? right stores = none ↔
      ∃ i, left.seed? (stores i) = none ∨ right.seed? (stores i) = none := by
  classical
  unfold Seeded.refinementOverStores? combineStoreVerdicts
  split
  · rename_i typed
    have all := (all_typed left right stores).mp typed
    simp only [reduceCtorEq, false_iff]
    rintro ⟨i, bad | bad⟩
    · simpa [bad] using (all i).1
    · simpa [bad] using (all i).2
  · rename_i invalid
    simp only [true_iff]
    by_contra noBad
    apply invalid
    apply (all_typed left right stores).mpr
    intro i
    refine ⟨Option.isSome_iff_ne_none.mpr fun h => noBad ⟨i, Or.inl h⟩,
      Option.isSome_iff_ne_none.mpr fun h => noBad ⟨i, Or.inr h⟩⟩

theorem eq_some (verdict : Bool) :
    left.refinementOverStores? right stores = some verdict ↔
      (∀ i, (left.seed? (stores i)).isSome = true ∧ (right.seed? (stores i)).isSome = true) ∧
      (verdict = true ↔ ∀ i (policy : Silmaril.Logic.ITree.Model.{0,0} signature.traceSignature.toSignature),
        ∀ x, policy.initial x → ∀ trace,
          HandledTrace policy.step x (observeRaw signature.primitive exits fields source (stores i)) trace →
          HandledTrace policy.step x (observeRaw signature.primitive exits fields target (stores i)) trace) := by
  rw [Seeded.refinementOverStores?, combine_eq_some]
  simp only [List.forall_mem_ofFn_iff, store_isSome, Bool.and_eq_true]
  refine and_congr_right fun all => iff_congr Iff.rfl (forall_congr' fun i => ?_)
  simp only [Seeded.refinementFromStore?_eq_some_iff, true_iff, ← Seeded.seed?_eq_some_iff,
    ← Option.isSome_iff_exists, (all i).1, (all i).2, true_and]

end Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Public.Stores
