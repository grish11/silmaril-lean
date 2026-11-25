module

public import Silmaril.SSA.Isotope.LetIter.AbortSequence.Thms
public import Silmaril.SSA.Isotope.LetIter.Categorical.Empty.Thms
public import Silmaril.SSA.Isotope.LetIter.Categorical.Soundness.Thms
import Silmaril.Proofs.SSA.Isotope.LetIter.Categorical.AbortSequence

/-! # Categorical semantics of explicit empty elimination -/

public section

namespace Silmaril.Isotope.LetIter.Semantics.Categorical

open Silmaril.Isotope.LetIter.LocallyNameless
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory

universe u v w r u₁ u₂ v₁ v₂

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  [FreydCategory.CentralUnit J]
  {τ : Type u} [TypeFormers τ] {ν : Type w} [DecidableEq ν]
  {Φ : Type v} [HasTy Φ τ] {Γ : Ctx ν τ}
  (M : TypeModel τ V) [InstructionModel J M Φ]

local notation "tensorIso" => Functor.StrongPremonoidal.tensorIso (J := J)

/-- Explicit empty elimination preserves denotation in a typing-coherent central-unit model. -/
theorem denote_abortSequence (coherent : TypingCoherent (ν := ν) J M Φ)
    {n : Nat} {β : BoundCtx τ n} {a b : Tm ν Φ n} {A : τ}
    (h : AbortSequence Γ β a b A) (da : Derivation Φ Γ β a A) (db : Derivation Φ Γ β b A) :
    denote J M da = denote J M db :=
  denote_abortSequence_proof J M coherent h da db

variable {ε : Type r} [HasEff Φ ε] {pe : ε}

/-- The separate abort-sequencing extension is sound with the exact theory's model premises. -/
theorem denote_abortEquiv_of_coherent_shared_tensor
    (coherent : TypingCoherent (ν := ν) J M Φ)
    (shared : ∀ R S : V, ∃ e : J.obj R ⊗ J.obj S = J.obj (R ⊗ S), tensorIso R S = eqToIso e)
    (pureInstr : ∀ f : Φ, IsPure pe f → ∃ p : M.obj (instrSrc f) ⟶ M.obj (instrTrg f),
      InstructionModel.denote (J := J) (M := M) f = J.map p)
    {n : Nat} {β : BoundCtx τ n} {a b : Tm ν Φ n} {A : τ}
    (h : AbortEquiv pe Γ β a b A) (da : Derivation Φ Γ β a A) (db : Derivation Φ Γ β b A) :
    denote J M da = denote J M db :=
  denote_abortEquiv_of_coherent_shared_tensor_proof J M coherent shared pureInstr h da db

end Silmaril.Isotope.LetIter.Semantics.Categorical
