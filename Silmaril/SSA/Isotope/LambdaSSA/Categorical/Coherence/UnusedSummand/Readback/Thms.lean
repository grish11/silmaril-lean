module

public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.UnusedSummand.Readback.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.UnusedSummand.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.CfgReadback.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.UnusedSummand
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.UnusedSummandFamily

/-! # Compare actual CFG witnesses after recovering their label families -/

public section

universe u v u₁ u₂ v₁ v₂

namespace Silmaril.Isotope.LambdaSSA.Semantics.Categorical.UnusedSummand

open CategoryTheory CategoryTheory.Limits
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.UnusedSummandProof

variable {κ : Type u} {Φ : Type v} [HasTy Φ (Ty κ)]

/-- If each label is targeted by a written local jump, its payload type has
the common or widened shape dictated by the renderer. -/
theorem Program.family_from_typing {n : Nat} {R S : Fin n → Ty κ} {L : LCtx (Ty κ)}
    {Γ : VCtx (Ty κ)} (p : Program (Φ := Φ) R L Γ) (covers : p.targetsEveryLabel)
    (tag : Bool) (he : (p.entry.region tag id).HasType Γ (List.ofFn S ++ L))
    (hb : ∀ i, ((p.blocks i).region tag Nat.succ).HasType (S i :: Γ) (List.ofFn S ++ L)) :
    ∃ tails : Option (Fin n → Ty κ), tails.isSome = tag ∧ S = family R tails :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.UnusedSummandFamily.family_from_typing
    p covers tag he hb

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C]
  (J : V ⥤ C) [StrongElgotFreydCategory J]
  (M : TypeModel (Ty κ) V) [InstructionModel J M Φ]

variable {n : Nat} {R : Fin (n + 1) → Ty κ} {L : LCtx (Ty κ)} {Γ : VCtx (Ty κ)}

/-- Every actual witness at a compatible family gives the same common arrow.
This comparison uses the entry, rows and collective arrow supplied by that
witness. -/
theorem Program.denotesAt_agree (p : Program (Φ := Φ) R L Γ) (roll : IterationRolling C) :
    ∃ f : J.obj (ctxObj M Γ) ⟶ J.obj (labelObj M L), ∀ tails : Option (Fin (n + 1) → Ty κ),
      p.denotesAt J M tails f ∧ ∀ g, p.denotesAt J M tails g → g = f :=
  program_at_agreement J M roll p

/-- Read back the family used by an arbitrary top-level witness. Coverage
is about written jump targets, including targets in both arms of a case. -/
theorem Program.denotes_readback (p : Program (Φ := Φ) R L Γ) (covers : p.targetsEveryLabel)
    {tag : Bool} {t : (p.region tag).HasType Γ L}
    {f : J.obj (ctxObj M Γ) ⟶ J.obj (labelObj M L)} (d : RegionDenotes J M t f) :
    ∃ tails : Option (Fin (n + 1) → Ty κ), tails.isSome = tag ∧ p.denotesAt J M tails f :=
  program_witness_readback J M p covers d

/-- Compare arbitrary exact graph witnesses of the common or widened
renderings when the written jumps constrain all internal labels. -/
theorem Program.denotes_eq (p : Program (Φ := Φ) R L Γ) (roll : IterationRolling C)
    (covers : p.targetsEveryLabel) {tag tag' : Bool}
    {t : (p.region tag).HasType Γ L} {t' : (p.region tag').HasType Γ L}
    {f g : J.obj (ctxObj M Γ) ⟶ J.obj (labelObj M L)}
    (d : RegionDenotes J M t f) (e : RegionDenotes J M t' g) : f = g :=
  program_witness_eq J M roll p covers d e

end Silmaril.Isotope.LambdaSSA.Semantics.Categorical.UnusedSummand
