module

public import Silmaril.SSA.Isotope.Institution.Relational.LetIter.Defs

public section

namespace Silmaril.Isotope.Institution.Relational.LetIter

open CategoryTheory Semantics Theory Silmaril.Logic.Metatheory.TheoryModel
open Silmaril.Isotope.LetIter.LocallyNameless

universe u v

variable {τ ε ν : Type u} [DecidableEq ν] [TypeFormers τ]
variable {Γ : Ctx ν τ} {P Q : InstrSig τ ε}
variable {D : τ → Type v} [ProductModel D] [UnitModel D] [CoproductModel D]

private theorem syntaxOp_cast_op {n : Nat} {β : BoundCtx τ n} (f : Q.Instr)
    {A B : τ} (hs : instrSrc f = A) (ht : instrTrg f = B)
    (p : Program Q Γ ⟨n, β, A⟩) :
    let o := castOp (Models.signature Q.Instr Γ)
      (congrArg (fun C => (⟨n, β, C⟩ : TypingIndex τ)) ht)
      (Models.Operation.op (Γ := Γ) (β := β) f)
    ∀ (args : (j : Fin o.arity) → Program Q Γ (o.argSort j)),
      (∀ j, HEq (args j) p) →
      Models.syntaxOp o args = ⟨.op f p.1, ht ▸ .op (hs.symm ▸ p.2)⟩ := by
  cases hs
  cases ht
  dsimp only
  intro args ha
  have h : args = fun _ => p := funext fun j => eq_of_heq (ha j)
  subst args
  rfl

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

/-- Fold the exact syntax into the reduct of the target syntax. -/
private abbrev foldSyntax (g : P ⟶ Q) {n : Nat} {β : BoundCtx τ n}
    {t : Tm ν P.Instr n} {A : τ} (d : Derivation P.Instr Γ β t A) :
    Program Q Γ ⟨n, β, A⟩ :=
  Models.denote (Algebra.reductObj (Silmaril.Isotope.Institution.LetIter.sigHom Γ g)
    (Models.syntaxAlgebra Q.Instr Γ)) d

private theorem foldSyntax_op (g : P ⟶ Q) {n : Nat} {β : BoundCtx τ n}
    (op : P.Instr) {t : Tm ν P.Instr n} (d : Derivation P.Instr Γ β t (instrSrc op)) :
    foldSyntax g (.op (f := op) d) =
      ⟨.op (g.instr op) (foldSyntax g d).1,
        g.target op ▸ .op ((g.source op).symm ▸ (foldSyntax g d).2)⟩ := by
  let o := Models.Operation.op (Γ := Γ) (β := β) op
  change Models.syntaxOp (Silmaril.Isotope.Institution.LetIter.opMap Γ g o)
    (fun j => Eq.rec (motive := fun i _ => Program Q Γ i) (foldSyntax g d)
      (Silmaril.Isotope.Institution.LetIter.argSortMap Γ g o j)) = _
  exact syntaxOp_cast_op (g.instr op) (g.source op) (g.target op) _ _
    (fun _ => eqRec_heq _ _)

theorem translate_eq_fold_proof (g : P ⟶ Q) {i : TypingIndex τ}
    (p : Program P Γ i) :
    Program.translate g p =
      Models.denote (Algebra.reductObj (Silmaril.Isotope.Institution.LetIter.sigHom Γ g)
        (Models.syntaxAlgebra Q.Instr Γ)) p.2 := by
  let X := Algebra.reductObj (Silmaril.Isotope.Institution.LetIter.sigHom Γ g)
    (Models.syntaxAlgebra Q.Instr Γ)
  change ((Models.syntaxIsInitial P.Instr Γ).to X).map p = Models.denote X p.2
  rw [Models.syntaxIsInitial_to]
  rfl

theorem translate_op_proof (g : P ⟶ Q) {n : Nat} {β : BoundCtx τ n}
    (op : P.Instr) (p : Program P Γ ⟨n, β, instrSrc op⟩) :
    Program.translate g (⟨.op op p.1, .op p.2⟩ : Program P Γ ⟨n, β, instrTrg op⟩) =
      ⟨.op (g.instr op) (Program.translate g p).1,
        g.target op ▸ .op ((g.source op).symm ▸ (Program.translate g p).2)⟩ := by
  let source : Program P Γ ⟨n, β, instrTrg op⟩ := ⟨.op op p.1, .op p.2⟩
  let target (a : Program Q Γ ⟨n, β, instrSrc op⟩) :
      Program Q Γ ⟨n, β, instrTrg op⟩ :=
    ⟨.op (g.instr op) a.1, g.target op ▸ .op ((g.source op).symm ▸ a.2)⟩
  exact (translate_eq_fold_proof g source).trans
    ((foldSyntax_op g op p.2).trans (congrArg target (translate_eq_fold_proof g p).symm))

private theorem denoteRelation_fold (g : P ⟶ Q) (M : Model D Q)
    {n : Nat} {β : BoundCtx τ n} {t : Tm ν P.Instr n} {A : τ}
    (d : Derivation P.Instr Γ β t A) :
    ∀ (γ : FreeEnv D Γ) (ρ : BoundEnv D β) (b : D A),
      (foldSyntax g d).2.denoteRelation D M γ ρ b ↔
        d.denoteRelation D (M.reduct g) γ ρ b := by
  induction d with
  | fv | bv | unit => intros; rfl
  | @op n β op _ ha ih =>
      intro γ ρ b
      rw [foldSyntax_op g op ha]
      exact (denoteRelation_cast_op M (g.instr op) (g.source op) (g.target op)
        (foldSyntax g ha).2 γ ρ b).trans (exists_congr fun a => and_congr (ih γ ρ a) Iff.rfl)
  | let₁ _ _ iha ihb =>
      intro γ ρ b
      exact exists_congr fun a => and_congr (iha γ ρ a) (ihb γ (ρ.snoc a) b)
  | pair _ _ iha ihb =>
      intro γ ρ p
      exact exists_congr fun a => and_congr (iha γ ρ a)
        (exists_congr fun b => and_congr (ihb γ ρ b) Iff.rfl)
  | let₂ _ _ iha ihb =>
      intro γ ρ b
      exact exists_congr fun ab =>
        let p := ProductModel.productEquiv (D := D) _ _ ab
        and_congr (iha γ ρ ab) (ihb γ ((ρ.snoc p.1).snoc p.2) b)
  | inl _ ih | inr _ ih =>
      intro γ ρ b
      exact exists_congr fun a => and_congr (ih γ ρ a) Iff.rfl
  | case _ _ _ ihe ihl ihr =>
      intro γ ρ b
      refine exists_congr fun e => and_congr (ihe γ ρ e) ?_
      cases CoproductModel.coprodEquiv (D := D) _ _ e with
      | inl a => exact ihl γ (ρ.snoc a) b
      | inr a => exact ihr γ (ρ.snoc a) b
  | abort => intros; rfl
  | iter _ _ iha ihb =>
      intro γ ρ b
      refine exists_congr fun a => and_congr (iha γ ρ a) ?_
      have sameStep := fun s r =>
        ihb γ (ρ.snoc s) ((CoproductModel.coprodEquiv (D := D) _ _).symm r)
      exact ⟨Relation.Iterates.mono (fun s r => (sameStep s r).mp),
        Relation.Iterates.mono (fun s r => (sameStep s r).mpr)⟩

/-- Agreement with the native evaluator through the existing presented syntax fold. -/
theorem denoteRelation_translate_proof (g : P ⟶ Q) (M : Model D Q)
    {i : TypingIndex τ} (p : Program P Γ i) (γ : FreeEnv D Γ)
    (ρ : BoundEnv D i.bound) (b : D i.result) :
    (Program.translate g p).2.denoteRelation D M γ ρ b ↔
      p.2.denoteRelation D (M.reduct g) γ ρ b := by
  obtain ⟨n, β, A⟩ := i
  rw [translate_eq_fold_proof]
  exact denoteRelation_fold g M p.2 γ ρ b

end Silmaril.Isotope.Institution.Relational.LetIter
