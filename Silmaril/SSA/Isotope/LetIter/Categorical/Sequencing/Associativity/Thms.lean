module

public import Silmaril.SSA.Isotope.LetIter.Categorical.Sequencing.Thms
import Silmaril.Proofs.SSA.Isotope.LetIter.Categorical.Sequencing.Associativity

/-! # Native LetIter sequencing with a central context diagonal -/

public section

namespace Silmaril.Isotope.LetIter.Semantics.Categorical

open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory PremonoidalCategory
open scoped MonoidalCategory
open Silmaril.Isotope.LetIter.LocallyNameless
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (duplicate)

universe u v w u₁ u₂ v₁ v₂

variable {τ : Type u} [TypeFormers τ] {ν : Type w} [DecidableEq ν]
  {Φ : Type v} [HasTy Φ τ] {Γ : Ctx ν τ}
  {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  (M : TypeModel τ V) [InstructionModel J M Φ]

local notation "Env" => envObj M Γ
local notation "tensorIso" => Functor.StrongPremonoidal.tensorIso (J := J)

/-- Binding an effectful let reassociates when the original context diagonal is central. -/
theorem denote_bind_let_of_diagonal {n : Nat} {β : BoundCtx τ n}
    {a : Tm ν Φ n} {b c : Tm ν Φ (n + 1)} {A B D : τ}
    (central : IsCentral
      (J.map (duplicate (Env β)) ≫ (tensorIso (Env β) (Env β)).inv))
    (da : Derivation Φ Γ β a A) (db : Derivation Φ Γ (.snoc β A) b B)
    (dc : Derivation Φ Γ (.snoc β B) c D) :
    denote J M (.let₁ (.let₁ da db) dc) =
      denote J M (.let₁ da (.let₁ db
        (dc.rename (TypedRenaming.underBinder β A B)))) :=
  denote_bind_let_of_diagonal_proof J M central da db dc

/-- An effectful continuation can run in either branch under centrality of the original context diagonal. -/
theorem denote_bind_let_case_of_diagonal {n : Nat} {β : BoundCtx τ n}
    {e : Tm ν Φ n} {l r c : Tm ν Φ (n + 1)} {A B D F : τ}
    (central : IsCentral
      (J.map (duplicate (Env β)) ≫ (tensorIso (Env β) (Env β)).inv))
    (de : Derivation Φ Γ β e (coprod A B))
    (dl : Derivation Φ Γ (.snoc β A) l D) (dr : Derivation Φ Γ (.snoc β B) r D)
    (dc : Derivation Φ Γ (.snoc β D) c F) :
    denote J M (.let₁ (.case de dl dr) dc) =
      denote J M (.case de
        (.let₁ dl (dc.rename (TypedRenaming.underBinder β A D)))
        (.let₁ dr (dc.rename (TypedRenaming.underBinder β B D)))) :=
  denote_bind_let_case_of_diagonal_proof J M central de dl dr dc

/-- A let after product elimination can run inside the two product binders. -/
theorem denote_bind_let_pair_of_diagonal {n : Nat} {β : BoundCtx τ n}
    {a : Tm ν Φ n} {b : Tm ν Φ (n + 2)} {c : Tm ν Φ (n + 1)} {A B D F : τ}
    (central : IsCentral
      (J.map (duplicate (Env β)) ≫ (tensorIso (Env β) (Env β)).inv))
    (da : Derivation Φ Γ β a (product A B))
    (db : Derivation Φ Γ (.snoc (.snoc β A) B) b D)
    (dc : Derivation Φ Γ (.snoc β D) c F) :
    denote J M (.let₁ (.let₂ da db) dc) =
      denote J M (.let₂ da (.let₁ db
        ((dc.rename (TypedRenaming.underBinder β A D)).rename
          (TypedRenaming.underBinder (.snoc β A) B D)))) :=
  denote_bind_let_pair_of_diagonal_proof J M central da db dc

/-- Eliminating a constructed pair sequences both computations in order under centrality of the two retained diagonals. -/
theorem denote_pair_beta_of_diagonals {n : Nat} {β : BoundCtx τ n}
    {a b : Tm ν Φ n} {c : Tm ν Φ (n + 2)} {A B D : τ}
    (central : IsCentral
      (J.map (duplicate (Env β)) ≫ (tensorIso (Env β) (Env β)).inv))
    (centralExtended : IsCentral
      (J.map (duplicate (Env β ⊗ M.obj A)) ≫
        (tensorIso (Env β ⊗ M.obj A) (Env β ⊗ M.obj A)).inv))
    (da : Derivation Φ Γ β a A) (db : Derivation Φ Γ β b B)
    (dc : Derivation Φ Γ (.snoc (.snoc β A) B) c D) :
    denote J M (.let₂ (.pair da db) dc) =
      denote J M (.let₁ da (.let₁ (db.lift (B := A)) dc)) :=
  denote_pair_beta_of_diagonals_proof J M central centralExtended da db dc

end Silmaril.Isotope.LetIter.Semantics.Categorical
