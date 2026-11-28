module

public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.UnusedSummand.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.UnusedSummand
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.UnusedSummandTyping

/-! # Factorization for exact CFG witnesses with unused summands -/

public section

universe u v u₁ u₂ v₁ v₂

namespace Silmaril.Isotope.LambdaSSA.Semantics.Categorical.UnusedSummand

open CategoryTheory CategoryTheory.Limits
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)

variable {κ : Type u} {Φ : Type v} [HasTy Φ (Ty κ)]

/-- An operand synthesizes the same exact result type after any typed value
renaming. In a term let, this also fixes the initializer's binder type. -/
theorem Operand.typeDetermined {Γ Δ : VCtx (Ty κ)} {A : Ty κ} {ρ : Nat → Nat}
    (a : Operand (Φ := Φ) Γ A) (ren : Ren Γ Δ ρ) :
    TypeDetermined Δ (a.term.rename ρ) A :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.UnusedSummandTyping.operand_type ren a

/-- The operand fixes every intermediate term type after typed renaming, so
its exact graph witnesses agree by `DeterminedTerm.denotes_eq`. -/
theorem Operand.determined {Γ Δ : VCtx (Ty κ)} {A : Ty κ} {ρ : Nat → Nat}
    (a : Operand (Φ := Φ) Γ A) (ren : Ren Γ Δ ρ) :
    DeterminedTerm Δ (a.term.rename ρ) A :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.UnusedSummandTyping.operand_determined ren a

/-- An exact typing for a rendered row at the selected label family. -/
theorem Row.hasType {n : Nat} {R : Fin n → Ty κ} {L : LCtx (Ty κ)} {Γ Δ : VCtx (Ty κ)}
    {ρ : Nat → Nat} (r : Row (Φ := Φ) R L Γ) (ren : Ren Γ Δ ρ)
    (tails : Option (Fin n → Ty κ)) :
    (r.region tails.isSome ρ).HasType Δ (List.ofFn (family R tails) ++ L) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.UnusedSummandTyping.row_typed ren tails r

/-- Both the common and widened label families type the actual written CFG. -/
theorem Program.hasType {n : Nat} {R : Fin n → Ty κ} {L : LCtx (Ty κ)} {Γ : VCtx (Ty κ)}
    (p : Program (Φ := Φ) R L Γ) (tails : Option (Fin n → Ty κ)) :
    (p.region tails.isSome).HasType Γ L :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.UnusedSummandTyping.program_typed p tails

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C]
  (J : V ⥤ C) [StrongElgotFreydCategory J]
  (M : TypeModel (Ty κ) V) [InstructionModel J M Φ]

/-- The typed row forces the exact factorization for any witnesses at the
selected interfaces. The environment map reads the retained variables.
Outward payloads keep their types, and local payloads receive the left tag. -/
theorem Row.denote_cut_of_renaming {n : Nat} {R D : Fin n → Ty κ} {L : LCtx (Ty κ)}
    {Γ Δ : VCtx (Ty κ)} {ρ : Nat → Nat} (r : Row (Φ := Φ) R L Γ) (ren : Ren Γ Δ ρ)
    (p : ctxObj M Δ ⟶ ctxObj M Γ)
    (reads : ∀ ⦃i A⦄ (h : At Γ i A), p ≫ lookup M i h = lookup M (ρ i) (ren h))
    {ts : (r.region false id).HasType Γ (List.ofFn R ++ L)}
    {tl : (r.region true ρ).HasType Δ (List.ofFn (family R (some D)) ++ L)}
    {f : J.obj (ctxObj M Γ) ⟶ J.obj (labelObj M (List.ofFn R ++ L))}
    {g : J.obj (ctxObj M Δ) ⟶ J.obj (labelObj M (List.ofFn (family R (some D)) ++ L))}
    (small : RegionDenotes J M ts f) (wide : RegionDenotes J M tl g) :
    g ≫ J.map (labelAppendSplit M (List.ofFn (family R (some D))) L) =
      J.map p ≫ f ≫ J.map (labelAppendSplit M (List.ofFn R) L) ≫
        J.map (coprod.map (𝟙 (labelObj M L)) (embedLabels M R D)) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.UnusedSummandProof.row_comparison
    J M ren p reads D r small wide

/-- There is one arrow with exact CFG graph witnesses for the common family
and every widened family. The proof assembles the actual collective block
arrows and uses ordinary rolling at the retained contextual steps. -/
theorem Program.denotes_agree {n : Nat} {R : Fin (n + 1) → Ty κ} {L : LCtx (Ty κ)}
    {Γ : VCtx (Ty κ)} (p : Program (Φ := Φ) R L Γ) (roll : IterationRolling C) :
    ∃ f, ∀ tails : Option (Fin (n + 1) → Ty κ), RegionDenotes J M (p.hasType tails) f := by
  obtain ⟨f, agree⟩ :=
    Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.UnusedSummandProof.program_agreement J M roll p
  exact ⟨f, fun tails => agree tails (p.hasType tails)⟩

end Silmaril.Isotope.LambdaSSA.Semantics.Categorical.UnusedSummand
