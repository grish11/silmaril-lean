module

public import Silmaril.SSA.Isotope.Institution.Relational.LetIter.Defs

public section

namespace Silmaril.Isotope.Institution.Relational.LetIter

open CategoryTheory Semantics Theory
open Silmaril.Isotope.LetIter.LocallyNameless

universe u v w

variable {τ ε : Type u} {ν : Type w} [DecidableEq ν] [TypeFormers τ]
variable {Γ : Ctx ν τ} {P Q R : InstrSig τ ε}
variable {D : τ → Type v} [ProductModel D] [UnitModel D] [CoproductModel D]

private theorem mapDerivation_cast (g : P ⟶ Q) {n : Nat} {β : BoundCtx τ n}
    {t : Tm ν P.Instr n} {A B : τ} (h : A = B) (d : Derivation P.Instr Γ β t A) :
    mapDerivation g (h ▸ d : Derivation P.Instr Γ β t B) =
      (h ▸ mapDerivation g d : Derivation Q.Instr Γ β (t.mapInstr g.instr) B) := by
  cases h
  rfl

theorem mapDerivation_id_proof {n : Nat} {β : BoundCtx τ n} {t : Tm ν P.Instr n}
    {A : τ} (d : Derivation P.Instr Γ β t A) :
    HEq (mapDerivation (𝟙 P) d) d := by
  induction d <;> simp only [mapDerivation] <;> congr 1 <;> exact Tm.mapInstr_id _

theorem mapDerivation_comp_proof (f : P ⟶ Q) (g : Q ⟶ R)
    {n : Nat} {β : BoundCtx τ n} {t : Tm ν P.Instr n}
    {A : τ} (d : Derivation P.Instr Γ β t A) :
    HEq (mapDerivation (f ≫ g) d) (mapDerivation g (mapDerivation f d)) := by
  induction d <;> simp only [mapDerivation]
  case op n β op t ha ih =>
    dsimp only [Tm.mapInstr]
    rw [mapDerivation_cast]
    dsimp only [mapDerivation, Tm.mapInstr]
    simp only [eqRec_heq_iff, heq_eqRec_iff]
    congr 1
    · exact (Tm.mapInstr_comp f.instr g.instr _).symm
    · simp only [eqRec_heq_iff, heq_eqRec_iff]
      rw [mapDerivation_cast g (f.source op).symm (mapDerivation f ha)]
      exact heq_eqRec_iff.mpr ih
  all_goals congr 1 <;> exact (Tm.mapInstr_comp f.instr g.instr _).symm

private theorem denoteRelation_cast_op (M : Model D Q) (f : Q.Instr)
    {n : Nat} {β : BoundCtx τ n} {t : Tm ν Q.Instr n} {A B : τ}
    (hs : instrSrc f = A) (ht : instrTrg f = B) (d : Derivation Q.Instr Γ β t A)
    (γ : FreeEnv D Γ) (ρ : BoundEnv D β) (b : D B) :
    Derivation.denoteRelation D M
      (ht ▸ .op (f := f) (hs.symm ▸ d) : Derivation Q.Instr Γ β (.op f t) B) γ ρ b ↔
      ∃ a, d.denoteRelation D M γ ρ a ∧
        M.eval f (cast (congrArg D hs.symm) a) (cast (congrArg D ht.symm) b) := by
  cases hs
  cases ht
  rfl

theorem denoteRelation_translate_proof (g : P ⟶ Q) (M : Model D Q)
    {n : Nat} {β : BoundCtx τ n} {t : Tm ν P.Instr n} {A : τ}
    (d : Derivation P.Instr Γ β t A) :
    ∀ (γ : FreeEnv D Γ) (ρ : BoundEnv D β) (b : D A),
      (mapDerivation g d).denoteRelation D M γ ρ b ↔
        d.denoteRelation D (M.reduct g) γ ρ b := by
  induction d with
  | fv | bv | unit => intros; rfl
  | @op _ _ op _ ha ih =>
      intro γ ρ b
      exact (denoteRelation_cast_op M (g.instr op) (g.source op) (g.target op)
        (mapDerivation g ha) γ ρ b).trans (exists_congr fun a => and_congr (ih γ ρ a) Iff.rfl)
  | let₁ _ _ iha ihb | pair _ _ iha ihb | let₂ _ _ iha ihb =>
      intro γ ρ b
      dsimp only [mapDerivation, Tm.mapInstr, Derivation.denoteRelation]
      simp only [iha, ihb]
  | inl _ ih | inr _ ih =>
      intro γ ρ b
      dsimp only [mapDerivation, Tm.mapInstr, Derivation.denoteRelation]
      simp only [ih]
  | case _ _ _ ihe ihl ihr =>
      intro γ ρ b
      dsimp only [mapDerivation, Tm.mapInstr, Derivation.denoteRelation]
      refine exists_congr fun e => and_congr (ihe γ ρ e) ?_
      cases CoproductModel.coprodEquiv (D := D) _ _ e with
      | inl a => exact ihl γ (ρ.snoc a) b
      | inr a => exact ihr γ (ρ.snoc a) b
  | abort => intros; rfl
  | iter _ _ iha ihb =>
      intro γ ρ b
      dsimp only [mapDerivation, Tm.mapInstr, Derivation.denoteRelation]
      refine exists_congr fun a => and_congr (iha γ ρ a) ?_
      have sameStep := fun s r =>
        ihb γ (ρ.snoc s) ((CoproductModel.coprodEquiv (D := D) _ _).symm r)
      exact ⟨Relation.Iterates.mono (fun s r => (sameStep s r).mp),
        Relation.Iterates.mono (fun s r => (sameStep s r).mpr)⟩

end Silmaril.Isotope.Institution.Relational.LetIter
