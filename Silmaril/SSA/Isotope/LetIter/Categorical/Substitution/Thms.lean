module

public import Silmaril.SSA.Isotope.LetIter.Categorical.Substitution.Defs
public import Silmaril.SSA.Isotope.LetIter.Categorical.Coherence.Defs
import Silmaril.Proofs.SSA.Isotope.LetIter.Categorical.Substitution

/-! # Renaming, pure substitution and pure let β in exact categorical LetIter -/

public section

universe u v w u₁ u₂ v₁ v₂

namespace Silmaril.Isotope.LetIter.Semantics.Categorical

open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory
open scoped MonoidalCategory
open Silmaril.Isotope.LetIter.LocallyNameless

variable {τ : Type u} [TypeFormers τ] {ν : Type w} [DecidableEq ν]
  {Φ : Type v} [HasTy Φ τ] {Γ : Ctx ν τ}
  {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  (M : TypeModel τ V) [InstructionModel J M Φ]

/-- Typed renaming precomposes the denotation by the corresponding value environment map. -/
theorem denote_rename {n m : Nat} {β : BoundCtx τ n} {δ : BoundCtx τ m}
    {t : Tm ν Φ n} {A : τ} (d : Derivation Φ Γ β t A) (ρ : TypedRenaming β δ) :
    denote J M (d.rename ρ) = J.map (envRenameMap M Γ ρ) ≫ denote J M d :=
  denote_rename_proof J M d ρ

/-- Weakening forgets the inserted bound variable. -/
theorem denote_lift {n : Nat} {β : BoundCtx τ n} {t : Tm ν Φ n} {A B : τ}
    (d : Derivation Φ Γ β t A) :
    denote J M (d.lift (B := B)) = J.map (dropSlot M β B) ≫ denote J M d :=
  denote_lift_proof J M d

/-- Weakening below the newest binder drops the inserted slot and retains the newest value. -/
theorem denote_underBinder {n : Nat} {β : BoundCtx τ n}
    {t : Tm ν Φ (n + 1)} {A X Y : τ} (d : Derivation Φ Γ (.snoc β Y) t A) :
    J.map (envSnocIso M Γ (.snoc β X) Y).hom ≫
        denote J M (d.rename (TypedRenaming.underBinder β X Y)) =
      J.map (dropSlot M β X ▷ M.obj Y) ≫
        J.map (envSnocIso M Γ β Y).hom ≫ denote J M d :=
  denote_underBinder_proof J M d

/-- Simultaneous substitution by value denotations precomposes the bound environment tuple. -/
theorem denote_bsubst {n m : Nat} {β : BoundCtx τ n} {δ : BoundCtx τ m}
    {t : Tm ν Φ n} {A : τ} (d : Derivation Φ Γ β t A)
    {σ : Fin n → Tm ν Φ m} (s : DerivSubst (Γ := Γ) β δ σ)
    (p : ∀ i, envObj M Γ δ ⟶ M.obj (β.get i)) (hs : ∀ i, denote J M (s i) = J.map (p i)) :
    denote J M (d.bsubst s) = J.map (envSubstMap M Γ β δ p) ≫ denote J M d :=
  denote_bsubst_proof J M d s p hs

/-- Instantiation with a value pairs the current environment with that value. -/
theorem denote_instantiate {n : Nat} {β : BoundCtx τ n}
    {a : Tm ν Φ n} {b : Tm ν Φ (n + 1)} {A B : τ}
    (da : Derivation Φ Γ β a A) (db : Derivation Φ Γ (.snoc β A) b B)
    (f : envObj M Γ β ⟶ M.obj A) (hf : denote J M da = J.map f) :
    denote J M (db.instantiate da) =
      J.map (lift (𝟙 (envObj M Γ β)) f ≫ (envSnocIso M Γ β A).hom) ≫ denote J M db :=
  denote_instantiate_proof J M da db f hf

variable {ε : Type*} [HasEff Φ ε] {pe : ε}
variable (pureInstr : ∀ f : Φ, IsPure pe f →
  ∃ p : M.obj (instrSrc f) ⟶ M.obj (instrTrg f),
    InstructionModel.denote (J := J) (M := M) f = J.map p)

include pureInstr

/-- Pure substitution images supply a value map for the whole bound environment. -/
theorem denote_pure_bsubst {n m : Nat} {β : BoundCtx τ n} {δ : BoundCtx τ m}
    {t : Tm ν Φ n} {A : τ} (d : Derivation Φ Γ β t A)
    {σ : Fin n → Tm ν Φ m} (s : DerivSubst (Γ := Γ) β δ σ)
    (hs : ∀ i, Pure pe (σ i)) :
    ∃ p : ∀ i, envObj M Γ δ ⟶ M.obj (β.get i),
      (∀ i, denote J M (s i) = J.map (p i)) ∧
        denote J M (d.bsubst s) = J.map (envSubstMap M Γ β δ p) ≫ denote J M d :=
  denote_pure_bsubst_proof J M pureInstr d s hs

/-- The pure let-β rule at its constructed substitution witness. -/
theorem denote_let_beta {n : Nat} {β : BoundCtx τ n}
    {a : Tm ν Φ n} {b : Tm ν Φ (n + 1)} {A B : τ}
    (da : Derivation Φ Γ β a A) (db : Derivation Φ Γ (.snoc β A) b B) (p : Pure pe a) :
    denote J M (.let₁ da db) = denote J M (db.instantiate da) :=
  denote_let_beta_proof J M pureInstr da db p

/-- In a typing-coherent model, pure let β holds at any endpoint derivations. -/
theorem denote_let_beta_of_coherent {n : Nat} {β : BoundCtx τ n}
    {a : Tm ν Φ n} {b : Tm ν Φ (n + 1)} {A B : τ}
    (coherent : TypingCoherent (ν := ν) J M Φ)
    (da : Derivation Φ Γ β a A) (db : Derivation Φ Γ (.snoc β A) b B) (p : Pure pe a)
    (l : Derivation Φ Γ β (.let₁ a b) B) (r : Derivation Φ Γ β (Tm.instantiate b a) B) :
    denote J M l = denote J M r :=
  (coherent l _).trans ((denote_let_beta J M pureInstr da db p).trans (coherent _ r))

end Silmaril.Isotope.LetIter.Semantics.Categorical
