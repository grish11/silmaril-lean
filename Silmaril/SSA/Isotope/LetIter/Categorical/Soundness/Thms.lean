module

public import Silmaril.SSA.Isotope.LetIter.Categorical.Coherence.Thms
public import Silmaril.SSA.Isotope.LetIter.Categorical.Sequencing.Uniformity.Thms
import Silmaril.Proofs.SSA.Isotope.LetIter.Categorical.Soundness

/-! # Categorical soundness for native LetIter equations -/

public section

namespace Silmaril.Isotope.LetIter.Semantics.Categorical

open Silmaril.Isotope.LetIter.LocallyNameless
open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory PremonoidalCategory
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical
  (duplicate)
open scoped MonoidalCategory

universe u v w u₁ u₂ v₁ v₂
variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]




variable {τ : Type u} [TypeFormers τ] {ν : Type w} [DecidableEq ν]
  {Φ : Type v} [HasTy Φ τ] {Γ : Ctx ν τ}
  (M : TypeModel τ V) [InstructionModel J M Φ]
  {ε : Type*} [HasEff Φ ε] {pe : ε}

variable [FreydCategory.CentralUnit J]

local notation "tensorIso" => Functor.StrongPremonoidal.tensorIso (J := J)

/-- Every native core axiom is sound at arbitrary endpoint derivations in a typing-coherent model with shared tensor comparisons. -/
theorem denote_core_of_coherent_shared_tensor
    (coherent : TypingCoherent (ν := ν) J M Φ)
    (shared : ∀ R S : V, ∃ e : J.obj R ⊗ J.obj S = J.obj (R ⊗ S), tensorIso R S = eqToIso e)
    (pureInstr : ∀ f : Φ, IsPure pe f → ∃ p : M.obj (instrSrc f) ⟶ M.obj (instrTrg f),
      InstructionModel.denote (J := J) (M := M) f = J.map p)
    {n : Nat} {β : BoundCtx τ n} {a b : Tm ν Φ n} {A : τ}
    (hax : CoreAxiom pe a b) (l : Derivation Φ Γ β a A) (r : Derivation Φ Γ β b A) :
    denote J M l = denote J M r :=
  denote_core_of_coherent_shared_tensor_proof J M coherent shared pureInstr hax l r

/-- Native LetIter equational derivability preserves denotation in a typing-coherent model with the paper's shared tensor comparisons. -/
theorem denote_equiv_of_coherent_shared_tensor
    (coherent : TypingCoherent (ν := ν) J M Φ)
    (shared : ∀ R S : V, ∃ e : J.obj R ⊗ J.obj S = J.obj (R ⊗ S), tensorIso R S = eqToIso e)
    (pureInstr : ∀ f : Φ, IsPure pe f → ∃ p : M.obj (instrSrc f) ⟶ M.obj (instrTrg f),
      InstructionModel.denote (J := J) (M := M) f = J.map p)
    {n : Nat} {β : BoundCtx τ n} {a b : Tm ν Φ n} {A : τ}
    (h : Equiv pe Γ β a b A) (da : Derivation Φ Γ β a A) (db : Derivation Φ Γ β b A) :
    denote J M da = denote J M db :=
  denote_equiv_of_coherent_shared_tensor_proof J M coherent shared pureInstr h da db

end Silmaril.Isotope.LetIter.Semantics.Categorical
