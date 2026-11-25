module

public import Silmaril.SSA.Isotope.LetIter.AbortSequence.Thms
public import Silmaril.SSA.Isotope.LetIter.Categorical.Empty.Thms
public import Silmaril.SSA.Isotope.LetIter.Categorical.Soundness.Thms

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

theorem denote_abortSequence_proof (coherent : TypingCoherent (ν := ν) J M Φ)
    {n : Nat} {β : BoundCtx τ n} {a b : Tm ν Φ n} {A : τ}
    (h : AbortSequence Γ β a b A) (da : Derivation Φ Γ β a A) (db : Derivation Φ Γ β b A) :
    denote J M da = denote J M db := by
  cases h with
  | sequence ha =>
    obtain ⟨d⟩ := Derivation.ofHasType ha
    exact (coherent da _).trans ((denote_let_abort J M d A).symm.trans (coherent _ db))
  | unsequence ha =>
    obtain ⟨d⟩ := Derivation.ofHasType ha
    exact (coherent da _).trans ((denote_let_abort J M d A).trans (coherent _ db))

variable {ε : Type r} [HasEff Φ ε] {pe : ε}

theorem denote_abortEquiv_of_coherent_shared_tensor_proof
    (coherent : TypingCoherent (ν := ν) J M Φ)
    (shared : ∀ R S : V, ∃ e : J.obj R ⊗ J.obj S = J.obj (R ⊗ S), tensorIso R S = eqToIso e)
    (pureInstr : ∀ f : Φ, IsPure pe f → ∃ p : M.obj (instrSrc f) ⟶ M.obj (instrTrg f),
      InstructionModel.denote (J := J) (M := M) f = J.map p)
    {n : Nat} {β : BoundCtx τ n} {a b : Tm ν Φ n} {A : τ}
    (h : AbortEquiv pe Γ β a b A) (da : Derivation Φ Γ β a A) (db : Derivation Φ Γ β b A) :
    denote J M da = denote J M db := by
  let related : TypedRelation ν Φ τ := fun {_} δ l r B =>
    ∃ (dl : Derivation Φ Γ δ l B) (dr : Derivation Φ Γ δ r B), denote J M dl = denote J M dr
  have closed : Refinement.Closed pe Γ (AbortSequence Γ) related := {
    equiv := fun eq => by
      obtain ⟨l⟩ := Derivation.ofHasType eq.hasType.1
      obtain ⟨r⟩ := Derivation.ofHasType eq.hasType.2
      exact ⟨l, r, denote_equiv_of_coherent_shared_tensor J M coherent shared pureInstr eq l r⟩
    primitive := fun law ha hb => by
      obtain ⟨l⟩ := Derivation.ofHasType ha
      obtain ⟨r⟩ := Derivation.ofHasType hb
      exact ⟨l, r, denote_abortSequence_proof J M coherent law l r⟩
    trans := fun ⟨l, m₁, h₁⟩ ⟨m₂, r, h₂⟩ =>
      ⟨l, r, h₁.trans ((coherent m₁ m₂).trans h₂)⟩
    op := fun ⟨l, r, hden⟩ => ⟨.op l, .op r, by simp only [denote, hden]⟩
    let₁ := fun ⟨l, r, scrutinee⟩ ⟨b, c, body⟩ =>
      ⟨.let₁ l b, .let₁ r c, by simp only [denote, scrutinee, body]⟩
    pair := fun ⟨l₁, r₁, eq₁⟩ ⟨l₂, r₂, eq₂⟩ =>
      ⟨.pair l₁ l₂, .pair r₁ r₂, by simp only [denote, eq₁, eq₂]⟩
    let₂ := fun ⟨l, r, scrutinee⟩ ⟨b, c, body⟩ =>
      ⟨.let₂ l b, .let₂ r c, by simp only [denote, scrutinee, body]⟩
    inl := fun ⟨l, r, hden⟩ => ⟨.inl l, .inl r, by simp only [denote, hden]⟩
    inr := fun ⟨l, r, hden⟩ => ⟨.inr l, .inr r, by simp only [denote, hden]⟩
    case := fun ⟨e, e', he⟩ ⟨l, l', hl⟩ ⟨r, r', hr⟩ =>
      ⟨.case e l r, .case e' l' r', by simp only [denote, he, hl, hr]⟩
    abort := fun ⟨l, r, hden⟩ => ⟨.abort l, .abort r, by simp only [denote, hden]⟩
    iter := fun ⟨l, r, initial⟩ ⟨b, c, body⟩ =>
      ⟨.iter l b, .iter r c, by simp only [denote, initial, body]⟩
  }
  obtain ⟨l, r, hden⟩ := h.least closed
  exact (coherent da l).trans (hden.trans (coherent r db))

end Silmaril.Isotope.LetIter.Semantics.Categorical
