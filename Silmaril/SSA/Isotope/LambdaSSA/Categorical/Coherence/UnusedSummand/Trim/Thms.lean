module

public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.UnusedSummand.Readback.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.UnusedSummandFamily
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.UnusedSummandTrim.Dispatch

/-! # Exact witness agreement after restricting to written CFG targets -/

public section

universe u v u₁ u₂ v₁ v₂

namespace Silmaril.Isotope.LambdaSSA.Semantics.Categorical.UnusedSummand

open CategoryTheory CategoryTheory.Limits
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)

variable {κ : Type u} {Φ : Type v} [HasTy Φ (Ty κ)]

/-- Exact typing determines the common or widened shape at every written
jump target. The types of labels with no written incoming jump are unrestricted. -/
theorem Program.targets_from_typing {n : Nat} {R S : Fin n → Ty κ} {L : LCtx (Ty κ)}
    {Γ : VCtx (Ty κ)} (p : Program (Φ := Φ) R L Γ)
    (tag : Bool) (he : (p.entry.region tag id).HasType Γ (List.ofFn S ++ L))
    (hb : ∀ i, ((p.blocks i).region tag Nat.succ).HasType (S i :: Γ) (List.ofFn S ++ L)) :
    ∃ tails : Option (Fin n → Ty κ), tails.isSome = tag ∧
      ∀ i, p.targets i → S i = family R tails i :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.UnusedSummandFamily.targets_from_typing
    p tag he hb

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C]
  (J : V ⥤ C) [StrongElgotFreydCategory J]
  (M : TypeModel (Ty κ) V) [InstructionModel J M Φ]

/-- Compare arbitrary exact graph witnesses of a nonempty rendered CFG.
Rolling restricts feedback to the coproduct of labels targeted anywhere in
the written entry or rows. Both case arms count, including unreachable ones.
If no local label is targeted, the entry uses only outward exits. -/
theorem Program.denotes_eq_trimmed {n : Nat} {R : Fin (n + 1) → Ty κ} {L : LCtx (Ty κ)}
    {Γ : VCtx (Ty κ)} (p : Program (Φ := Φ) R L Γ) (roll : IterationRolling C)
    {tag tag' : Bool} {t : (p.region tag).HasType Γ L} {t' : (p.region tag').HasType Γ L}
    {f g : J.obj (ctxObj M Γ) ⟶ J.obj (labelObj M L)}
    (d : RegionDenotes J M t f) (e : RegionDenotes J M t' g) : f = g :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.UnusedSummandTrim.compare_trimmed J M p roll d e

end Silmaril.Isotope.LambdaSSA.Semantics.Categorical.UnusedSummand
