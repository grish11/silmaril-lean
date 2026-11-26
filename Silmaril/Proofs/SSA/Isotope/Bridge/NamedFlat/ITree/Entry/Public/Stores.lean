module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Public.Stores.Defs
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Public.Construction.Thms
import Mathlib.Data.List.OfFn

public section

namespace Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Public.Stores

open Silmaril.Isotope
open Silmaril.Isotope.Bridge.NamedFlat.Entry.Public (Seeded)
open Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut (observeRaw)
open Silmaril.SSA.LambdaRTL (CFG)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible
open Silmaril.Elgot.ITree (HandledTrace)

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
  unfold Seeded.refinementOverStores?
  dsimp only
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
  unfold Seeded.refinementOverStores?
  dsimp only
  split
  · rename_i typed
    have all := (all_typed left right stores).mp typed
    have passes :
        (List.ofFn fun i => left.refinementFromStore? right (stores i)).all (· == some true) = true ↔
          ∀ i (policy : Silmaril.Logic.ITree.Model.{0,0} signature.traceSignature.toSignature),
            ∀ x, policy.initial x → ∀ trace,
              HandledTrace policy.step x (observeRaw signature.primitive exits fields source (stores i)) trace →
              HandledTrace policy.step x (observeRaw signature.primitive exits fields target (stores i)) trace := by
      rw [List.all_eq_true, List.forall_mem_ofFn_iff]
      exact forall_congr' fun i => by
        simp only [beq_iff_eq, Seeded.refinementFromStore?_eq_some_iff, true_iff,
          ← Seeded.seed?_eq_some_iff, ← Option.isSome_iff_exists, (all i).1, (all i).2, true_and]
    rw [Option.some.injEq, Bool.eq_iff_iff, passes]
    exact ⟨fun h => ⟨all, h.symm⟩, fun h => h.2.symm⟩
  · rename_i invalid
    simp only [reduceCtorEq, false_iff]
    exact fun h => invalid ((all_typed left right stores).mpr h.1)

end Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Public.Stores
