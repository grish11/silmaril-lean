module

public import Silmaril.SSA.Isotope.LetParIter.Categorical.Kleisli.Defs
public import Silmaril.SSA.Isotope.LetParIter.Categorical.Soundness.Thms
import Silmaril.Proofs.SSA.Isotope.LetParIter.Categorical.Kleisli

/-! # Fixed-witness native soundness and mixed soundness in the canonical Kleisli model -/

public section

namespace Silmaril.Isotope.LetParIter.Categorical

open CategoryTheory Silmaril.Elgot
open Parallel (Derivation)
open LetIter.ProofRelevant.Semantics (TypeModel InstructionModel)

universe u v w q r

variable {τ : Type u} [TypeFormers τ] [Subtyping τ] [TypeModel.{u, v} τ]
  {ν : Type r} [DecidableEq ν] {Φ : Type w} [HasTy Φ τ]
  {ε : Type q} [HasEff Φ ε] [Bot ε]
  {m : Type v → Type v} [Monad m] [LawfulMonad m] [Iterate m] [LawfulElgotMonad m]
  [InstructionModel Φ τ ε m] [∀ X Y : Kleisli (ofTypeMonad m), Preorder (X ⟶ Y)]

local notation "K" => Kleisli.Adjunction.toKleisli (ofTypeMonad m)

/-- `Equiv.native` preserves the canonical Kleisli evaluator at the supplied witnesses. -/
theorem native_sound_of_type (P : FreydCategory.OrderedParallel K) :
    letI := kleisliInstructionModel (τ := τ) (Φ := Φ) (ε := ε) (m := m)
    FixedNativeSound (ν := ν) (Φ := Φ) K P (kleisliTypeModel τ) (⊥ : ε) :=
  native_sound_of_type_proof P

/-- The entire generated mixed equivalence preserves Kleisli denotation. The model supplies
ordered parallel and the two arrow-level laws in `Laws`. The canonical tensor comparison
and primitive interpretation discharge centrality and purity. -/
theorem sound_of_type (P : FreydCategory.OrderedParallel K) (L : Laws K P)
    {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n} {a b : Tm ν Φ n} {A : τ}
    {da : Derivation Φ Γ β a A} {db : Derivation Φ Γ β b A} (h : Equiv (⊥ : ε) Γ da db) :
    letI := kleisliInstructionModel (τ := τ) (Φ := Φ) (ε := ε) (m := m)
    denote K P (kleisliTypeModel τ) da = denote K P (kleisliTypeModel τ) db :=
  sound_of_type_proof P L h

end Silmaril.Isotope.LetParIter.Categorical
