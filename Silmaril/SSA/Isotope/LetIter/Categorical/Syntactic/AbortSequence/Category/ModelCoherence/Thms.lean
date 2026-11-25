module

public import Silmaril.SSA.Isotope.LetIter.Categorical.Coherence.FreeContext.Thms
public import Silmaril.SSA.Isotope.LetIter.Categorical.Syntactic.AbortSequence.Category.ModelReflection.Thms

/-! # Typing coherence of repaired LetIter denotation -/

public section

universe u

namespace Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic

open CategoryTheory
open Silmaril.Isotope.LetIter.LocallyNameless (Refinement)
open Silmaril.Thesis.LambdaIter.Syn.SynCat (ValueCat values)

variable {τ Φ ε : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] (pe : ε)
  [SymmetricPremonoidalCategory (RepairedSynCat (τ := τ) (Φ := Φ) pe)]
  [DistributivePremonoidalCategory (RepairedSynCat (τ := τ) (Φ := Φ) pe)]
  [StrongElgotFreydCategory (repairedValues (τ := τ) (Φ := Φ) pe)]
  [InstructionModel (repairedValues (τ := τ) (Φ := Φ) pe) (typeModel (τ := τ) (Φ := Φ) pe) Φ]

/-- Reflection on empty free contexts gives full typing coherence for the
repaired model with no free names, including contexts with anonymous slots. -/
theorem repairedTypingCoherent
    (tensorHom : ∀ R A : ValueCat (signature (τ := τ) (Φ := Φ) pe),
      (repairedProjection pe).map
        (Functor.StrongPremonoidal.tensorIso (J := values (signature pe)) R A).hom =
      (Functor.StrongPremonoidal.tensorIso (J := repairedValues pe) R A).hom)
    (instr : ∀ f : Φ, (repairedProjection pe).map ((instructionModel (τ := τ) pe).denote f) =
      InstructionModel.denote (J := repairedValues pe) (M := typeModel (τ := τ) (Φ := Φ) pe) f) :
    TypingCoherent (ν := Empty) (repairedValues (τ := τ) (Φ := Φ) pe) (typeModel (τ := τ) (Φ := Φ) pe) Φ := by
  apply typingCoherent_empty_of_nil (repairedValues (Φ := Φ) pe) (typeModel pe)
  intro n β t A d e
  exact (repairedModel_denote_eq_iff pe tensorHom instr d e).mpr (Refinement.refl d.toHasType)

end Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic
