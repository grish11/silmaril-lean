module

public import Silmaril.SSA.RVSDG.LambdaSSA.Gamma.Categorical.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Thms
import Silmaril.Proofs.SSA.RVSDG.LambdaSSA.Gamma

/-! # Scoped terminal γ translation and categorical soundness -/

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Isotope.LambdaSSA (Tm)
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical (ctxObj Denotes TypingCoherent denote)
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)

universe u v d h c k
variable {τ : Type u} {Φ : Type v} [TypeFormers τ] [HasTy Φ τ]
variable {Γ : List τ} {A : τ} {extra : Nat} {t : Tm Φ}

abbrev GammaGraph (Φ : Type v) [HasTy Φ τ]
    (extra : Nat) (Γ : List τ) (A : τ) :=
  Graph (Opcode Φ) (.control (extra + 2) :: inputs Γ) [] [[.value A]] [.value A]

abbrev GammaGraphRelated (t : Tm Φ) (g : GammaGraph Φ extra Γ A) :=
  GammaRelated extra t g.toTerm

@[expose] def lowerGammaGraph (h : GammaSSAForm extra t Γ A) :
    Σ g : GammaGraph Φ extra Γ A, GammaGraphRelated t g :=
  let ⟨rv, rel⟩ := lowerGamma h
  ⟨rv.toGraph, by simpa only [GammaGraphRelated, Term.toTerm_toGraph] using rel⟩

@[expose] def raiseGammaGraph (g : GammaGraph Φ extra Γ A) (h : GammaRVForm extra g.toTerm) :
    Σ t : Tm Φ, GammaGraphRelated t g :=
  raiseGamma h

theorem GammaRelated.typing
    {rv : Term (Opcode Φ) (.control (extra + 2) :: inputs Γ) [] [[.value A]] [.value A]}
    (rel : GammaRelated extra t rv) : Tm.HasType (selectorType (extra + 1) :: Γ) t A := by
  cases rel with
  | intro arms => exact Proofs.switchTyping _ .head (fun i => .tail (arms i))

variable {D : Type d} {C : Type c} [Category.{h} D] [CartesianMonoidalCategory D]
  [HasFiniteCoproducts D] [SymmetricCategory D] [DistributiveTensor D]
  [Category.{k} C] [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts C] [DistributivePremonoidalCategory C]
  (J : D ⥤ C) [DistributiveFreydCategory J] (M : TypeModel τ D) [InstructionModel J M Φ]
  (sel : Categorical.Selectors D)
  (prim : ∀ f : Φ, M.obj (instrSrc f) ⟶ M.obj (instrTrg f))

/-- The actual λSSA case spine denotes the direct γ graph after transporting
the selector, ordered payload and singleton result. The theorem uses any
syntactic relation witness. -/
theorem GammaGraphRelated.sound {g : GammaGraph Φ extra Γ A} (rel : GammaGraphRelated t g) :
    ∃ f : ctxObj M (selectorType (extra + 1) :: Γ) ⟶ M.obj A,
      Denotes J M rel.typing (J.map f) ∧
      gammaEntryMap M sel prim extra Γ ≫ f =
        g.denote (valueModel M sel prim) ≫ (ρ_ (M.obj A)).hom := by
  rw [← Graph.denote_toTerm]
  exact Proofs.gamma_related_sound J M sel prim rel rel.typing

/-- In a coherent model the transported graph arrow is the chosen λSSA denotation. -/
theorem GammaGraphRelated.denote_eq [TypingCoherent (Φ := Φ) J M]
    {g : GammaGraph Φ extra Γ A} (rel : GammaGraphRelated t g) :
    J.map (gammaEntryMap M sel prim extra Γ) ≫ denote J M rel.typing =
      J.map (g.denote (valueModel M sel prim) ≫ (ρ_ (M.obj A)).hom) := by
  obtain ⟨f, d, h⟩ := rel.sound J M sel prim
  rw [← d.eq_denote, ← J.map_comp, h]

end Silmaril.SSA.RVSDG.LambdaSSA
