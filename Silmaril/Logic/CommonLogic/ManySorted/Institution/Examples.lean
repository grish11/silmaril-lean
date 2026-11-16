module

public import Silmaril.Logic.CommonLogic.ManySorted.Institution.Thms

/-! A genuine sort-identifying map with operation and relation symbols at every profile. -/
@[expose] public section
noncomputable section

namespace Silmaril.Logic.CommonLogic.ManySorted.Institution.Examples

open CategoryTheory Silmaril.Logic.Institution Silmaril.Logic.Institution.Examples
open Silmaril.Logic.CommonLogic

def twoSorted : FOL.Signature :=
  ⟨⟨Bool, fun _ _ _ => Unit⟩, fun _ _ => Unit⟩

def oneSorted : FOL.Signature :=
  ⟨⟨Unit, fun _ _ _ => Unit⟩, fun _ _ => Unit⟩

/-- This map identifies two distinct sorts, and maps every operation and relation profile. -/
def collapse : twoSorted ⟶ oneSorted where
  sorts := fun _ => ()
  ops := fun _ => ()
  rels := fun _ => ()

theorem collapse_not_injective : ¬ Function.Injective collapse.sorts := by
  intro h
  have bad : false = true := h (show collapse.sorts false = collapse.sorts true from rfl)
  cases bad

def numeric : FOL.Structure oneSorted where
  carrier := fun _ => Nat
  op := fun _ _ => 7
  rel := fun _ args => ∀ i, args i = 7

def target : TypedModel oneSorted := Expansion.expand numeric

def pulledBack : TypedModel twoSorted := (typedReduct collapse).obj target

/-- The two decoded carriers coincide after the actual sort-collapsing reduct. -/
theorem pulledBack_carriers :
    (decode pulledBack).carrier false = (decode pulledBack).carrier true := rfl

/-- Neither coinciding carrier is forced empty: it contains the tagged numeric value. -/
theorem pulledBack_inhabited : Nonempty ((decode pulledBack).carrier false) :=
  ⟨Expansion.pack numeric () (7 : Nat)⟩

/-- Strict decoder naturality holds for this map with all operation/relation profiles present. -/
theorem collapse_decode :
    decode pulledBack = (FOL.Structure.reduct collapse).obj (decode target) := rfl

/-- The bundled naturality square uses the real source signature map. -/
theorem collapse_comparison :
    FOL.corridor collapse ≫ comorphism.ρ.app oneSorted =
      comorphism.ρ.app twoSorted ≫ corridor collapse :=
  comorphism.ρ.naturality collapse

/-- Translation and satisfaction commute even though the signature map is not sort-injective. -/
theorem collapse_satisfaction (p : FOL.Sentence twoSorted) :
    (sentence (p.map collapse)).Holds target.obj Fin.elim0 Fin.elim0 ↔
      p.Holds ((FOL.Structure.reduct collapse).obj (decode target)) := by
  rw [← sentence_map collapse p]
  exact (Core.Formula.holds_map (signatureMap collapse) target.obj Fin.elim0 Fin.elim0
    (sentence p)).trans (sentence_holds pulledBack p).symm

end Silmaril.Logic.CommonLogic.ManySorted.Institution.Examples
