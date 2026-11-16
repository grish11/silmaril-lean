module

public import Silmaril.Logic.CommonLogic.FiniteListFOL.Translation.Defs
import Mathlib.Tactic.Tauto

@[expose] public section
namespace Silmaril.Proofs.Logic.CommonLogic.FiniteListFOLTranslation
open Silmaril.Logic.Institution.Examples
open Silmaril.Logic.CommonLogic
open Silmaril.Logic.CommonLogic.FiniteListFOL
open Silmaril.Logic.FirstOrder

/-- Fix the sort-valued motive before constructing a binary profile. -/
private abbrev sortPair {α : Type} (a b : α) : Fin 2 → α :=
  Fin.cases (motive := fun _ => α) a (fun _ => b)

private theorem eval_empty {Sg : EQ.Signature} (A : EQ.Algebra Sg)
    {m : Nat} {Γ : Fin m → Sg.S} (η : (i : Fin m) → A.carrier (Γ i))
    {s : Sg.S} (o : Sg.Op 0 Fin.elim0 s) :
    EQ.Term.eval A η (.app o (fun i => Fin.elim0 i)) =
      A.op o (fun i => Fin.elim0 i) := by
  unfold EQ.Term.eval
  congr 1
  funext i
  exact Fin.elim0 i

private theorem eval_tuple {Sg : EQ.Signature} (A : EQ.Algebra Sg)
    {m : Nat} {Γ : Fin m → Sg.S} (η : (i : Fin m) → A.carrier (Γ i))
    {a b : Sg.S} (t : EQ.Term Sg Γ a) (u : EQ.Term Sg Γ b) :
    (fun i : Fin 2 => EQ.Term.eval A η
      (Fin.cases (motive := fun i => EQ.Term Sg Γ (sortPair a b i))
        t (fun _ => u) i)) =
      Fin.cases (motive := fun i => A.carrier (sortPair a b i))
        (t.eval A η) (fun _ => u.eval A η) := by
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

private theorem eval_pair {Sg : EQ.Signature} (A : EQ.Algebra Sg)
    {m : Nat} {Γ : Fin m → Sg.S} (η : (i : Fin m) → A.carrier (Γ i))
    {a b s : Sg.S} (o : Sg.Op 2 (sortPair a b) s)
    (t : EQ.Term Sg Γ a) (u : EQ.Term Sg Γ b) :
    EQ.Term.eval A η (.app o (Fin.cases (motive := fun i => EQ.Term Sg Γ (sortPair a b i))
      t (fun _ => u))) =
      A.op o (Fin.cases (motive := fun i => A.carrier (sortPair a b i))
      (t.eval A η) (fun _ => u.eval A η)) := by
  exact congrArg (A.op o) (eval_tuple A η t u)

theorem weaken_eval {S : Core.Signature} (M : Model S) {m : Nat}
    {Γ : Fin m → FiniteLists.ListSort} {s : FiniteLists.ListSort}
    (bound : FiniteLists.ListSort) (t : Term S Γ s)
    (η : (i : Fin m) → M.obj.obj.carrier (Γ i)) (x : M.obj.obj.carrier bound) :
    (weaken bound t).eval M.obj.obj.toAlgebra (Fin.cases x η) =
      t.eval M.obj.obj.toAlgebra η := by
  have h := Variables.eval_rename
    (Sg := FiniteLists.publicSignature (signature S)) M.obj.obj t
    (Δ := Fin.cases bound Γ) Fin.succ (fun _ => rfl)
    (Variables.consAssignment M.obj.obj bound Γ x η)
  have hp : Variables.pullback
      (Sg := FiniteLists.publicSignature (signature S)) M.obj.obj
      (Γ := Γ) (Δ := Fin.cases bound Γ) Fin.succ (fun _ => rfl)
      (Variables.consAssignment M.obj.obj bound Γ x η) = η := by
    funext i
    rfl
  exact h.trans (congrArg (fun a => EQ.Term.eval M.obj.obj.toAlgebra a t) hp)

theorem term_eval {S : Core.Signature} (M : Model S) {n k m : Nat}
    {Γ : Fin m → FiniteLists.ListSort}
    (ρ : Fin n → Term S Γ .discourse) (σ : Fin k → Term S Γ .sequence)
    (ξ : Fin n → D M.obj) (ζ : Fin k → List (D M.obj))
    (η : (i : Fin m) → M.obj.obj.carrier (Γ i))
    (hρ : ∀ i, (ρ i).eval M.obj.obj.toAlgebra η = ξ i)
    (hσ : ∀ i, (σ i).eval M.obj.obj.toAlgebra η = FiniteLists.evaluationEquiv M.obj (ζ i))
    {a : Core.Kind} (t : Core.Expr S n k a) :
    (translateTerm ρ σ t).eval M.obj.obj.toAlgebra η =
      encodeValue M a (t.eval (decode M) ξ ζ) := by
  induction t with
  | var i => exact hρ i
  | name d =>
    dsimp only [translateTerm, Core.Expr.eval, encodeValue, decode]
    exact eval_empty M.obj.obj.toAlgebra η _
  | nonname r =>
    dsimp only [translateTerm, Core.Expr.eval, encodeValue, decode]
    exact eval_empty M.obj.obj.toAlgebra η _
  | lift t ih =>
    change embed M.obj _ = embed M.obj _
    exact congrArg (embed M.obj) ih
  | app r xs ihr ihxs =>
    have h := eval_pair
      (Sg := (FiniteLists.publicSignature (signature S)).toSignature)
      M.obj.obj.toAlgebra η (a := .reference) (b := .sequence) (s := .discourse)
      (.extra .apply) (translateTerm ρ σ r) (translateTerm ρ σ xs)
    exact h.trans (congrArg₂ (apply M.obj) ihr ihxs)
  | nil =>
    exact eval_empty M.obj.obj.toAlgebra η FiniteLists.Operation.nil
  | cons x xs ihx ihxs =>
    have h := eval_pair
      (Sg := (FiniteLists.publicSignature (signature S)).toSignature)
      M.obj.obj.toAlgebra η (a := .discourse) (b := .sequence) (s := .sequence)
      .cons (translateTerm ρ σ x) (translateTerm ρ σ xs)
    exact h.trans (congrArg₂ (FiniteLists.listReduct M.obj.obj).cons ihx ihxs)
  | marker m =>
    dsimp only [translateTerm, Core.Expr.eval, encodeValue, decode]
    rw [eval_empty]
    exact ((FiniteLists.evaluationEquiv M.obj).apply_symm_apply _).symm
  | seqvar i => exact hσ i
  | append xs ys ihxs ihys =>
    have h := eval_pair
      (Sg := (FiniteLists.publicSignature (signature S)).toSignature)
      M.obj.obj.toAlgebra η (a := .sequence) (b := .sequence) (s := .sequence)
      (.extra .append) (translateTerm ρ σ xs) (translateTerm ρ σ ys)
    exact (h.trans (congrArg₂ (append M.obj) ihxs ihys)).trans
      (append_evaluation M _ _)

/-- Satisfaction for every Core formula, arbitrary term substitutions and
arbitrary target sorted assignments. Both sequence quantifiers use the full
surjective actual-List evaluation equivalence. -/
theorem formula_holds {S : Core.Signature} (M : Model S) {n k : Nat}
    (p : Core.Formula S n k) : ∀ {m : Nat} {Γ : Fin m → FiniteLists.ListSort}
    (ρ : Fin n → Term S Γ .discourse) (σ : Fin k → Term S Γ .sequence)
    (ξ : Fin n → D M.obj) (ζ : Fin k → List (D M.obj))
    (η : (i : Fin m) → M.obj.obj.carrier (Γ i)),
    (∀ i, (ρ i).eval M.obj.obj.toAlgebra η = ξ i) →
    (∀ i, (σ i).eval M.obj.obj.toAlgebra η = FiniteLists.evaluationEquiv M.obj (ζ i)) →
    ((translateFormula ρ σ p).Holds M.obj.obj η ↔ p.Holds (decode M) ξ ζ) := by
  classical
  induction p with
  | equal t u =>
    intro m Γ ρ σ ξ ζ η hρ hσ
    change (translateTerm ρ σ t).eval M.obj.obj.toAlgebra η =
      (translateTerm ρ σ u).eval M.obj.obj.toAlgebra η ↔ _
    rw [term_eval M ρ σ ξ ζ η hρ hσ t, term_eval M ρ σ ξ ζ η hρ hσ u]
    rfl
  | pred r xs =>
    intro m Γ ρ σ ξ ζ η hρ hσ
    have ht := congrArg
      (fun args : (i : Fin 2) →
          M.obj.obj.carrier (FiniteLists.pair .reference .sequence i) =>
        M.obj.obj.rel Rel.holds args)
      (eval_tuple (Sg := (FiniteLists.publicSignature (signature S)).toSignature)
        M.obj.obj.toAlgebra η (a := .reference) (b := .sequence)
        (translateTerm ρ σ r) (translateTerm ρ σ xs))
    have hh := congrArg₂ (holds M.obj)
      (term_eval M ρ σ ξ ζ η hρ hσ r) (term_eval M ρ σ ξ ζ η hρ hσ xs)
    exact Iff.of_eq (ht.trans hh)
  | tt => intros; rfl
  | ff => intros; simp only [translateFormula, FOL.Formula.Holds, Core.Formula.Holds, not_true_eq_false]
  | neg p ih =>
    intro m Γ ρ σ ξ ζ η hρ hσ
    exact not_congr (ih ρ σ ξ ζ η hρ hσ)
  | conj p q ihp ihq =>
    intro m Γ ρ σ ξ ζ η hρ hσ
    exact and_congr (ihp ρ σ ξ ζ η hρ hσ) (ihq ρ σ ξ ζ η hρ hσ)
  | disj p q ihp ihq =>
    intro m Γ ρ σ ξ ζ η hρ hσ
    have hp := ihp ρ σ ξ ζ η hρ hσ
    have hq := ihq ρ σ ξ ζ η hρ hσ
    simp only [translateFormula, FOL.Formula.Holds, Core.Formula.Holds]
    tauto
  | impl p q ihp ihq =>
    intro m Γ ρ σ ξ ζ η hρ hσ
    have hp := ihp ρ σ ξ ζ η hρ hσ
    have hq := ihq ρ σ ξ ζ η hρ hσ
    simp only [translateFormula, FOL.Formula.Holds, Core.Formula.Holds]
    tauto
  | iff p q ihp ihq =>
    intro m Γ ρ σ ξ ζ η hρ hσ
    have hp := ihp ρ σ ξ ζ η hρ hσ
    have hq := ihq ρ σ ξ ζ η hρ hσ
    simp only [translateFormula, FOL.Formula.Holds, Core.Formula.Holds]
    tauto
  | all p ih =>
    intro m Γ ρ σ ξ ζ η hρ hσ
    rw [translateFormula, Variables.all_holds_cons]
    change (∀ x, _) ↔ ∀ x, _
    apply forall_congr'
    intro x
    apply ih (m := m + 1) (Γ := Fin.cases FiniteLists.ListSort.discourse Γ)
      (Fin.cases (.var 0 : Term S (Fin.cases FiniteLists.ListSort.discourse Γ) .discourse)
        (fun i => weaken .discourse (ρ i)))
      (fun i => weaken .discourse (σ i)) (Fin.cases x ξ) ζ
      (Variables.consAssignment M.obj.obj .discourse Γ x η)
    · intro i
      refine Fin.cases rfl (fun j => ?_) i
      exact (weaken_eval M .discourse (ρ j) η x).trans (hρ j)
    · intro i
      exact (weaken_eval M .discourse (σ i) η x).trans (hσ i)
  | ex p ih =>
    intro m Γ ρ σ ξ ζ η hρ hσ
    rw [translateFormula, Variables.exists_holds]
    change (∃ x, _) ↔ ∃ x, _
    apply exists_congr
    intro x
    apply ih (m := m + 1) (Γ := Fin.cases FiniteLists.ListSort.discourse Γ)
      (Fin.cases (.var 0 : Term S (Fin.cases FiniteLists.ListSort.discourse Γ) .discourse)
        (fun i => weaken .discourse (ρ i)))
      (fun i => weaken .discourse (σ i)) (Fin.cases x ξ) ζ
      (Variables.consAssignment M.obj.obj .discourse Γ x η)
    · intro i
      refine Fin.cases rfl (fun j => ?_) i
      exact (weaken_eval M .discourse (ρ j) η x).trans (hρ j)
    · intro i
      exact (weaken_eval M .discourse (σ i) η x).trans (hσ i)
  | allSeq p ih =>
    intro m Γ ρ σ ξ ζ η hρ hσ
    rw [translateFormula, Variables.all_holds_cons]
    change (∀ ys, _) ↔ ∀ xs : List (D M.obj), _
    constructor
    · intro hall xs
      exact (ih (m := m + 1) (Γ := Fin.cases FiniteLists.ListSort.sequence Γ)
        (fun i => weaken .sequence (ρ i))
        (Fin.cases (.var 0 : Term S (Fin.cases FiniteLists.ListSort.sequence Γ) .sequence)
          (fun i => weaken .sequence (σ i))) ξ (Fin.cases xs ζ)
        (Variables.consAssignment M.obj.obj .sequence Γ (FiniteLists.evaluationEquiv M.obj xs) η)
        (by intro i; exact (weaken_eval M .sequence (ρ i) η (FiniteLists.evaluationEquiv M.obj xs)).trans (hρ i))
        (by
          intro i
          refine Fin.cases rfl (fun j => ?_) i
          exact (weaken_eval M .sequence (σ j) η (FiniteLists.evaluationEquiv M.obj xs)).trans (hσ j))).mp
        (hall (FiniteLists.evaluationEquiv M.obj xs))
    · intro hall ys
      exact (ih (m := m + 1) (Γ := Fin.cases FiniteLists.ListSort.sequence Γ)
        (fun i => weaken .sequence (ρ i))
        (Fin.cases (.var 0 : Term S (Fin.cases FiniteLists.ListSort.sequence Γ) .sequence)
          (fun i => weaken .sequence (σ i))) ξ (Fin.cases ((FiniteLists.evaluationEquiv M.obj).symm ys) ζ)
        (Variables.consAssignment M.obj.obj .sequence Γ ys η)
        (by intro i; exact (weaken_eval M .sequence (ρ i) η ys).trans (hρ i))
        (by
          intro i
          refine Fin.cases ?_ (fun j => ?_) i
          · exact ((FiniteLists.evaluationEquiv M.obj).apply_symm_apply ys).symm
          · exact (weaken_eval M .sequence (σ j) η ys).trans (hσ j))).mpr
        (hall ((FiniteLists.evaluationEquiv M.obj).symm ys))
  | exSeq p ih =>
    intro m Γ ρ σ ξ ζ η hρ hσ
    rw [translateFormula, Variables.exists_holds]
    change (∃ ys, _) ↔ ∃ xs : List (D M.obj), _
    constructor
    · rintro ⟨ys, hys⟩
      refine ⟨(FiniteLists.evaluationEquiv M.obj).symm ys, ?_⟩
      exact (ih (m := m + 1) (Γ := Fin.cases FiniteLists.ListSort.sequence Γ)
        (fun i => weaken .sequence (ρ i))
        (Fin.cases (.var 0 : Term S (Fin.cases FiniteLists.ListSort.sequence Γ) .sequence)
          (fun i => weaken .sequence (σ i))) ξ (Fin.cases ((FiniteLists.evaluationEquiv M.obj).symm ys) ζ)
        (Variables.consAssignment M.obj.obj .sequence Γ ys η)
        (by intro i; exact (weaken_eval M .sequence (ρ i) η ys).trans (hρ i))
        (by
          intro i
          refine Fin.cases ?_ (fun j => ?_) i
          · exact ((FiniteLists.evaluationEquiv M.obj).apply_symm_apply ys).symm
          · exact (weaken_eval M .sequence (σ j) η ys).trans (hσ j))).mp hys
    · rintro ⟨xs, hxs⟩
      refine ⟨FiniteLists.evaluationEquiv M.obj xs, ?_⟩
      exact (ih (m := m + 1) (Γ := Fin.cases FiniteLists.ListSort.sequence Γ)
        (fun i => weaken .sequence (ρ i))
        (Fin.cases (.var 0 : Term S (Fin.cases FiniteLists.ListSort.sequence Γ) .sequence)
          (fun i => weaken .sequence (σ i))) ξ (Fin.cases xs ζ)
        (Variables.consAssignment M.obj.obj .sequence Γ (FiniteLists.evaluationEquiv M.obj xs) η)
        (by intro i; exact (weaken_eval M .sequence (ρ i) η (FiniteLists.evaluationEquiv M.obj xs)).trans (hρ i))
        (by
          intro i
          refine Fin.cases rfl (fun j => ?_) i
          exact (weaken_eval M .sequence (σ j) η (FiniteLists.evaluationEquiv M.obj xs)).trans (hσ j))).mpr hxs

theorem sentence_holds {S : Core.Signature} (M : Model S) (p : Core.Sentence S) :
    (sentence p).Holds M.obj.obj ↔ p.Holds (decode M) Fin.elim0 Fin.elim0 :=
  formula_holds M p Fin.elim0 Fin.elim0 Fin.elim0 Fin.elim0 (fun i => Fin.elim0 i)
    (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)

open CategoryTheory

theorem map_weaken {S T : Core.Signature} (f : S ⟶ T) {m : Nat}
    {Γ : Fin m → FiniteLists.ListSort} {s : FiniteLists.ListSort}
    (bound : FiniteLists.ListSort) (t : Term S Γ s) :
    (weaken bound t).map (FiniteLists.publicMap (signatureMap f)).toHom =
      weaken bound (t.map (FiniteLists.publicMap (signatureMap f)).toHom) := by
  refine EQ.Term.rec
    (motive := fun {_s} t =>
      (weaken bound t).map (FiniteLists.publicMap (signatureMap f)).toHom =
        weaken bound (t.map (FiniteLists.publicMap (signatureMap f)).toHom))
    ?_ ?_ t
  · intro i
    rfl
  · intro _ _ _ o args ih
    dsimp only [weaken, Variables.termRename, EQ.Term.map]
    congr 1
    funext i
    exact ih i

theorem map_consSubstitution {S T : Core.Signature} (f : S ⟶ T) {n m : Nat}
    {Γ : Fin m → FiniteLists.ListSort} (s : FiniteLists.ListSort)
    (ρ : Fin n → Term S Γ s) (i : Fin (n + 1)) :
    (Fin.cases (motive := fun _ : Fin (n + 1) => Term S (Fin.cases s Γ) s)
      (.var 0 : Term S (Fin.cases s Γ) s)
      (fun j => weaken s (ρ j)) i).map
        (FiniteLists.publicMap (signatureMap f)).toHom =
      Fin.cases (motive := fun _ : Fin (n + 1) => Term T (Fin.cases s Γ) s)
        (.var 0 : Term T (Fin.cases s Γ) s)
        (fun j => weaken s ((ρ j).map (FiniteLists.publicMap (signatureMap f)).toHom)) i := by
  have h : ∀ j : Fin n,
      (weaken s (ρ j)).map (FiniteLists.publicMap (signatureMap f)).toHom =
        weaken s ((ρ j).map (FiniteLists.publicMap (signatureMap f)).toHom) :=
    fun j => map_weaken f s (ρ j)
  exact Fin.cases (by rfl) h i

theorem term_map {S T : Core.Signature} (f : S ⟶ T) {n k m : Nat}
    {Γ : Fin m → FiniteLists.ListSort}
    (ρ : Fin n → Term S Γ .discourse) (σ : Fin k → Term S Γ .sequence)
    {a : Core.Kind} (t : Core.Expr S n k a) :
    (translateTerm ρ σ t).map (FiniteLists.publicMap (signatureMap f)).toHom =
      translateTerm
        (fun i => (ρ i).map (FiniteLists.publicMap (signatureMap f)).toHom)
        (fun i => (σ i).map (FiniteLists.publicMap (signatureMap f)).toHom) (t.map f) := by
  induction t with
  | var i => rfl
  | name d =>
    dsimp only [translateTerm, Core.Expr.map, EQ.Term.map,
      FiniteLists.publicMap, FiniteLists.Operation.map, signatureMap]
    congr 1
    funext i
    exact Fin.elim0 i
  | nonname r =>
    dsimp only [translateTerm, Core.Expr.map, EQ.Term.map,
      FiniteLists.publicMap, FiniteLists.Operation.map, signatureMap]
    congr 1
    funext i
    exact Fin.elim0 i
  | lift t ih =>
    simp only [translateTerm, Core.Expr.map, EQ.Term.map]
    congr 1
    funext i
    exact ih
  | app r xs ihr ihxs =>
    simp only [translateTerm, Core.Expr.map, EQ.Term.map]
    congr 1
    funext i
    exact Fin.cases ihr (fun _ => ihxs) i
  | nil =>
    dsimp only [translateTerm, Core.Expr.map, EQ.Term.map,
      FiniteLists.publicMap, FiniteLists.Operation.map, signatureMap]
    congr 1
    funext i
    exact Fin.elim0 i
  | cons x xs ihx ihxs =>
    simp only [translateTerm, Core.Expr.map, EQ.Term.map]
    congr 1
    funext i
    exact Fin.cases ihx (fun _ => ihxs) i
  | marker m =>
    dsimp only [translateTerm, Core.Expr.map, EQ.Term.map,
      FiniteLists.publicMap, FiniteLists.Operation.map, signatureMap]
    congr 1
    funext i
    exact Fin.elim0 i
  | seqvar i => rfl
  | append xs ys ihxs ihys =>
    simp only [translateTerm, Core.Expr.map, EQ.Term.map]
    congr 1
    funext i
    exact Fin.cases ihxs (fun _ => ihys) i

theorem formula_map {S T : Core.Signature} (f : S ⟶ T) {n k : Nat}
    (p : Core.Formula S n k) : ∀ {m : Nat} {Γ : Fin m → FiniteLists.ListSort}
    (ρ : Fin n → Term S Γ .discourse) (σ : Fin k → Term S Γ .sequence),
    (translateFormula ρ σ p).map (FiniteLists.publicMap (signatureMap f)) =
      translateFormula
        (fun i => (ρ i).map (FiniteLists.publicMap (signatureMap f)).toHom)
        (fun i => (σ i).map (FiniteLists.publicMap (signatureMap f)).toHom) (p.map f) := by
  induction p with
  | equal t u =>
    intro m Γ ρ σ
    dsimp only [translateFormula, Core.Formula.map, FOL.Formula.map]
    exact congrArg₂
      (fun (v w : Term T Γ .discourse) =>
        FOL.Formula.eq (Sg := FiniteLists.publicSignature (signature T)) v w)
      (term_map f ρ σ t) (term_map f ρ σ u)
  | pred r xs =>
    intros
    simp only [translateFormula, Core.Formula.map, FOL.Formula.map]
    congr 1
    funext i
    exact Fin.cases (term_map f _ _ r) (fun _ => term_map f _ _ xs) i
  | tt => intros; rfl
  | ff => intros; rfl
  | neg p ih => intros; simp only [translateFormula, Core.Formula.map, FOL.Formula.map, ih]
  | conj p q ihp ihq =>
    intros; simp only [translateFormula, Core.Formula.map, FOL.Formula.map, ihp, ihq]
  | disj p q ihp ihq =>
    intros; simp only [translateFormula, Core.Formula.map, FOL.Formula.map, ihp, ihq]
  | impl p q ihp ihq =>
    intros; simp only [translateFormula, Core.Formula.map, FOL.Formula.map, ihp, ihq]
  | iff p q ihp ihq =>
    intros; simp only [translateFormula, Core.Formula.map, FOL.Formula.map, ihp, ihq]
  | all p ih =>
    intro m Γ ρ σ
    have hc := funext (map_consSubstitution f FiniteLists.ListSort.discourse ρ)
    dsimp only [translateFormula, Core.Formula.map, FOL.Formula.map]
    rw [ih]
    rw [hc]
    simp_rw [map_weaken]
    rfl
  | ex p ih =>
    intro m Γ ρ σ
    have hc := funext (map_consSubstitution f FiniteLists.ListSort.discourse ρ)
    dsimp only [translateFormula, Core.Formula.map, Variables.existsFormula, FOL.Formula.map]
    rw [ih]
    rw [hc]
    simp_rw [map_weaken]
    rfl
  | allSeq p ih =>
    intro m Γ ρ σ
    have hc := funext (map_consSubstitution f FiniteLists.ListSort.sequence σ)
    dsimp only [translateFormula, Core.Formula.map, FOL.Formula.map]
    rw [ih]
    rw [hc]
    simp_rw [map_weaken]
    rfl
  | exSeq p ih =>
    intro m Γ ρ σ
    have hc := funext (map_consSubstitution f FiniteLists.ListSort.sequence σ)
    dsimp only [translateFormula, Core.Formula.map, Variables.existsFormula, FOL.Formula.map]
    rw [ih]
    rw [hc]
    simp_rw [map_weaken]
    rfl
theorem sentence_map {S T : Core.Signature} (f : S ⟶ T) (p : Core.Sentence S) :
    FOL.Sentence.map (FiniteLists.publicMap (signatureMap f)) (sentence p) =
      sentence (p.map f) := by
  unfold sentence FOL.Sentence.map
  have hρ : (fun i : Fin 0 =>
      (Fin.elim0 i : Term S Fin.elim0 .discourse).map
        (FiniteLists.publicMap (signatureMap f)).toHom) = Fin.elim0 := by
    funext i
    exact Fin.elim0 i
  have hσ : (fun i : Fin 0 =>
      (Fin.elim0 i : Term S Fin.elim0 .sequence).map
        (FiniteLists.publicMap (signatureMap f)).toHom) = Fin.elim0 := by
    funext i
    exact Fin.elim0 i
  congr 1
  exact (formula_map f p Fin.elim0 Fin.elim0).trans
    (congrArg₂ (fun ρ σ => translateFormula ρ σ (p.map f)) hρ hσ)

/-- Exact-object model expansion supplies a witness for satisfiable theories;
the corridor satisfaction condition handles both truth directions. -/
theorem corridor_sat_transport {S : Core.Signature}
    (c : Core.room S ⟶ room S) (hc : c.ModelExpansive)
    (H : Set (Core.Sentence S)) : Core.Sat H ↔ TargetSat (c.sen '' H) := by
  constructor
  · rintro ⟨M, hM⟩
    obtain ⟨N, hN⟩ := hc M
    refine ⟨N, ?_⟩
    rintro _ ⟨p, hp, rfl⟩
    apply (c.sat N p).mpr
    rw [hN]
    exact hM p hp
  · rintro ⟨N, hN⟩
    exact ⟨c.mod.obj N, fun p hp => (c.sat N p).mp (hN _ ⟨p, hp, rfl⟩)⟩

end Silmaril.Proofs.Logic.CommonLogic.FiniteListFOLTranslation
