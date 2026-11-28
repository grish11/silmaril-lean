module

public import Silmaril.Logic.ACL2.Defs

@[expose] public section

namespace Silmaril.Proofs.Logic.ACL2
open CategoryTheory Silmaril.Logic.ACL2

variable {S T U : Signature} {n m : Nat}

theorem map_id (t : Term S n) : t.map (𝟙 S) = t := by
  induction t <;> simp_all [Term.map, Signature.Hom.symbol]

theorem map_comp (σ : S ⟶ T) (τ : T ⟶ U) (t : Term S n) :
    t.map (σ ≫ τ) = (t.map σ).map τ := by
  induction t <;> simp_all [Term.map, Signature.Hom.symbol]

theorem map_subst (σ : S ⟶ T) (s : Fin n → Term S m) (t : Term S n) :
    (t.subst s).map σ = (t.map σ).subst (fun i => (s i).map σ) := by
  induction t <;> simp_all [Term.map, Term.subst]

theorem eval_map (σ : S ⟶ T) (M : Model T) (env : Fin n → M.primitives.Value) (t : Term S n) :
    (t.map σ).eval M env = t.eval (M.reduct σ) env := by
  induction t <;> simp_all [Term.map, Term.eval, Model.reduct]

theorem eval_subst (M : Model S) (env : Fin m → M.primitives.Value) (s : Fin n → Term S m)
    (t : Term S n) : (t.subst s).eval M env = t.eval M (fun i => (s i).eval M env) := by
  induction t <;> simp_all [Term.eval, Term.subst]

theorem reduct_id (S : Signature) :
    Model.functor (Model.reduct (𝟙 S)) = 𝟭 _ := by
  apply Functor.ext (fun _ => rfl)

theorem reduct_comp (σ : S ⟶ T) (τ : T ⟶ U) :
    Model.functor (Model.reduct (σ ≫ τ)) =
      Model.functor (Model.reduct τ) ⋙ Model.functor (Model.reduct σ) := by
  apply Functor.ext (fun _ => rfl)

theorem holds_eq (M : Model S) (x y : Term S n) :
    (Sentence.eq x y).Holds M ↔ ∀ env, x.eval M env = y.eval M env := by
  change (∀ env, M.primitives.equal (x.eval M env) (y.eval M env) ≠ M.primitives.nil) ↔ _
  simp [Primitives.equal, Primitives.ofBool, M.primitives.truth_ne_nil]

theorem bind {Γ Δ : Set (Sentence S)} {p : Sentence S}
    (h : Derives Γ p) (f : ∀ q ∈ Γ, Derives Δ q) : Derives Δ p := by
  induction h with
  | hyp hq => exact f _ hq
  | truth => exact .truth
  | refl x => exact .refl x
  | symm _ ih => exact .symm ih
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
  | congr body lhs rhs _ ih => exact .congr body lhs rhs ih
  | eqMp _ _ ih₁ ih₂ => exact .eqMp ih₁ ih₂
  | mp _ _ ih₁ ih₂ => exact .mp ih₁ ih₂
  | subst s _ ih => exact .subst s ih
  | carCons x y => exact .carCons x y
  | cdrCons x y => exact .cdrCons x y
  | conspCons x y => exact .conspCons x y
  | carAtom _ ih => exact .carAtom ih
  | cdrAtom _ ih => exact .cdrAtom ih
  | conspNil => exact .conspNil
  | conspTruth => exact .conspTruth
  | ifNil x y => exact .ifNil x y
  | ifTruth x y => exact .ifTruth x y
  | ifSame x y => exact .ifSame x y

theorem map_derives (σ : S ⟶ T) {Γ : Set (Sentence S)} {p : Sentence S}
    (h : Derives Γ p) : Derives (Sentence.map σ '' Γ) (p.map σ) := by
  induction h with
  | hyp hp => exact .hyp ⟨_, hp, rfl⟩
  | truth => exact .truth
  | refl x => exact .refl (x.map σ)
  | symm _ ih => exact .symm ih
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
  | congr body lhs rhs _ ih =>
    simpa only [Sentence.map, Sentence.eq, Term.map, map_subst] using
      Derives.congr (body.map σ) (fun i => (lhs i).map σ) (fun i => (rhs i).map σ) ih
  | eqMp _ _ ih₁ ih₂ => exact .eqMp ih₁ ih₂
  | mp _ _ ih₁ ih₂ => exact .mp ih₁ ih₂
  | subst s _ ih =>
    simpa only [Sentence.map, map_subst] using Derives.subst (fun i => (s i).map σ) ih
  | carCons x y => exact .carCons (x.map σ) (y.map σ)
  | cdrCons x y => exact .cdrCons (x.map σ) (y.map σ)
  | conspCons x y => exact .conspCons (x.map σ) (y.map σ)
  | carAtom _ ih => exact .carAtom ih
  | cdrAtom _ ih => exact .cdrAtom ih
  | conspNil => exact .conspNil
  | conspTruth => exact .conspTruth
  | ifNil x y => exact .ifNil (x.map σ) (y.map σ)
  | ifTruth x y => exact .ifTruth (x.map σ) (y.map σ)
  | ifSame x y => exact .ifSame (x.map σ) (y.map σ)

theorem sound {Γ : Set (Sentence S)} {p : Sentence S} (h : Derives Γ p) (M : Model S)
    (hΓ : ∀ q ∈ Γ, q.Holds M) : p.Holds M := by
  induction h with
  | hyp hp => exact hΓ _ hp
  | truth => exact fun _ => M.primitives.truth_ne_nil
  | refl => simp [holds_eq]
  | symm _ ih => exact (holds_eq ..).mpr fun env => ((holds_eq ..).mp ih env).symm
  | trans _ _ ih₁ ih₂ =>
    exact (holds_eq ..).mpr fun env => ((holds_eq ..).mp ih₁ env).trans ((holds_eq ..).mp ih₂ env)
  | congr body _ _ _ ih =>
    apply (holds_eq ..).mpr
    intro env
    simp only [eval_subst]
    exact congrArg (fun args => body.eval M args) (funext fun i => (holds_eq ..).mp (ih i) env)
  | eqMp _ _ ih₁ ih₂ => exact fun env => (holds_eq ..).mp ih₁ env ▸ ih₂ env
  | mp _ _ ih₁ ih₂ =>
    intro env
    have hp := ih₂ env
    have himp := ih₁ env
    change Term.eval M env _ ≠ M.primitives.nil at hp
    simp only [Term.implies, Term.eval, Primitives.ite, ite_eq_right hp] at himp
    by_contra hq
    exact himp (ite_eq_left hq)
  | subst s _ ih => exact fun env => (eval_subst M env s _).symm ▸ ih _
  | carCons => simp [holds_eq, Term.eval, M.primitives.car_cons]
  | cdrCons => simp [holds_eq, Term.eval, M.primitives.cdr_cons]
  | conspCons => simp [holds_eq, Term.eval, M.primitives.consp_cons, Primitives.ofBool]
  | carAtom _ ih =>
    apply (holds_eq ..).mpr
    intro env
    apply M.primitives.car_atom
    simpa [Term.eval, Primitives.ofBool, M.primitives.truth_ne_nil] using (holds_eq ..).mp ih env
  | cdrAtom _ ih =>
    apply (holds_eq ..).mpr
    intro env
    apply M.primitives.cdr_atom
    simpa [Term.eval, Primitives.ofBool, M.primitives.truth_ne_nil] using (holds_eq ..).mp ih env
  | conspNil => simp [holds_eq, Term.eval, M.primitives.consp_nil, Primitives.ofBool]
  | conspTruth => simp [holds_eq, Term.eval, M.primitives.consp_truth, Primitives.ofBool]
  | ifNil => simp [holds_eq, Term.eval, Primitives.ite]
  | ifTruth => simp [holds_eq, Term.eval, Primitives.ite, M.primitives.truth_ne_nil]
  | ifSame => simp [holds_eq, Term.eval, Primitives.ite]

end Silmaril.Proofs.Logic.ACL2
