module

public import Silmaril.SSA.Isotope.LetParIter.Categorical.Kleisli.Defs
public import Silmaril.SSA.Isotope.LetParIter.Categorical.Soundness.Thms
public import Silmaril.SSA.Isotope.LetIter.Categorical.Context.Thms

public section

namespace Silmaril.Isotope.LetParIter.Categorical

open CategoryTheory Silmaril.Elgot
open Parallel (Derivation)
open LetIter.ProofRelevant.Semantics (TypeModel InstructionModel categorical_sound)

universe u v w q r

variable {τ : Type u} [TypeFormers τ] [Subtyping τ] [TypeModel.{u, v} τ]
  {ν : Type r} [DecidableEq ν] {Φ : Type w} [HasTy Φ τ]
  {ε : Type q} [HasEff Φ ε] [Bot ε]
  {m : Type v → Type v} [Monad m] [LawfulMonad m] [Iterate m] [LawfulElgotMonad m]
  [InstructionModel Φ τ ε m] [∀ X Y : Kleisli (ofTypeMonad m), Preorder (X ⟶ Y)]

local notation "K" => Kleisli.Adjunction.toKleisli (ofTypeMonad m)
local notation "N" => LetIter.ProofRelevant.Semantics.Categorical.ofTypeModel (τ := τ)

set_option backward.isDefEq.respectTransparency false in
theorem native_sound_of_type_proof (P : FreydCategory.OrderedParallel K) :
    letI := kleisliInstructionModel (τ := τ) (Φ := Φ) (ε := ε) (m := m)
    FixedNativeSound (ν := ν) (Φ := Φ) K P (kleisliTypeModel τ) (⊥ : ε) := by
  intro Γ n β a b A da db related
  let instructions := LetIter.ProofRelevant.Semantics.Categorical.ofInstructionModel
    (τ := τ) (Φ := Φ) (ε := ε) (m := m)
  have ha := denote_embed_nativeTyping K P N da
  have hb := denote_embed_nativeTyping K P N db
  have sound := categorical_sound (m := m) related
  exact eq_of_heq (ha.trans (heq_of_eq sound) |>.trans hb.symm)

set_option backward.isDefEq.respectTransparency false in
theorem sound_of_type_proof (P : FreydCategory.OrderedParallel K) (L : Laws K P)
    {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n} {a b : Tm ν Φ n} {A : τ}
    {da : Derivation Φ Γ β a A} {db : Derivation Φ Γ β b A} (h : Equiv (⊥ : ε) Γ da db) :
    letI := kleisliInstructionModel (τ := τ) (Φ := Φ) (ε := ε) (m := m)
    denote K P (kleisliTypeModel τ) da = denote K P (kleisliTypeModel τ) db := by
  let inst := kleisliInstructionModel (τ := τ) (Φ := Φ) (ε := ε) (m := m)
  apply sound_of_native K P (kleisliTypeModel τ) L _ _ (native_sound_of_type_proof P) h
  · intro R
    exact LetIter.Semantics.Categorical.duplicate_central_of_tensor_eqToIso K R rfl rfl
  · intro f hp
    refine ⟨TypeCat.ofHom (InstructionModel.denotePure (m := m) f hp), Kleisli.hom_ext ?_⟩
    ext x
    exact InstructionModel.denote_pure (m := m) f hp x

end Silmaril.Isotope.LetParIter.Categorical
