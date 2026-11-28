module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Reverse.Flat.Defs

public section

namespace Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Reverse

open Silmaril.Isotope Silmaril.Isotope.LambdaSSA
open LambdaSSA.Acyclic LambdaSSA.Acyclic.Positional LambdaSSA.Acyclic.Positional.Capture
open LambdaSSA.Acyclic.Positional.Capture.Reverse

universe u v

variable {τ : Type u} {Φ : Type v} [TypeFormers τ] [HasTy Φ τ]
  {n k exits : Nat} {β : BoundCtx τ n} {R : Fin k → τ} {L : LCtx τ} {A : τ}

private theorem block_erase (b : Block Φ β R L A) (length : L.length = exits) : (b.toFlat length).erase = b.toSSA := by
  cases b <;> rfl

theorem toFlat_erase (c : CheckedTable Φ β L) (length : L.length = exits) :
    (c.toFlat length).erase = c.toSSA := by
  change Region.cfg _ _ (fun i => ((c.table.block i).toFlat length).erase) =
    Region.cfg _ _ (fun i => (c.table.block i).toSSA)
  rw [show (fun i => ((c.table.block i).toFlat length).erase) = (fun i => (c.table.block i).toSSA) from
    funext fun i => block_erase (c.table.block i) length]
  rfl

theorem toFlat_hasType {D : Fin exits → τ} (c : CheckedTable Φ β (List.ofFn D)) :
    (c.toFlat List.length_ofFn).HasType β c.table.types D := by
  constructor
  · apply Flat.hasType_of_erase
    change Region.HasType β.toList (c.table.entry 0 c.entry) _
    simpa only [SSA.FiniteSum.ofFn_append] using c.table.entry_hasType 0 c.entry
  · intro i
    apply Flat.hasType_of_erase
    change Region.HasType (β.snoc (c.table.types i)).toList
      ((c.table.block i).toFlat List.length_ofFn).erase _
    rw [block_erase]
    simpa only [SSA.FiniteSum.ofFn_append] using (c.table.block i).toSSA_hasType

omit [TypeFormers τ] in
private theorem target_locals (t : Target R L A) (length : L.length = exits) :
    Fin.addCases (fun j => [j]) (fun _ => []) (t.flatIndex length) = t.locals := by
  cases t with
  | «local» i => exact Fin.addCases_left i
  | @exit i _ h =>
    have bounded := (Target.exit (R := R) h).index_lt
    change k + i < k + L.length at bounded
    let j : Fin exits := ⟨i, length ▸ (Nat.lt_of_add_lt_add_left bounded)⟩
    change Fin.addCases (fun j => [j]) (fun _ => []) (j.natAdd k) = []
    exact Fin.addCases_right j

theorem toFlat_checked (c : CheckedTable Φ β L) (length : L.length = exits) :
    Rank.check (FlatLetCase.localTargets (c.toFlat length)) = true := by
  have eq : FlatLetCase.localTargets (c.toFlat length) = c.table.localTargets := by
    funext i
    change FlatLetCase.targets ((c.table.block i).toFlat length) = (c.table.block i).locals
    cases c.table.block i <;> simp only [Block.toFlat, Block.locals, FlatLetCase.targets, target_locals]
  rw [eq]
  exact c.checked

end Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Reverse
