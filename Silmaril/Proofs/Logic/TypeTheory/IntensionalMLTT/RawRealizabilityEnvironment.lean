module

public import Silmaril.Logic.TypeTheory.IntensionalMLTT.RawRealizability.Environment.Defs

@[expose] public section

open Silmaril.Logic.TypeTheory.IntensionalMLTT
open Silmaril.Logic.TypeTheory.IntensionalMLTT.RawRealizability

namespace Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRealizabilityEnvironment

private theorem eqv_map {α β : Sort _} {r : α → α → Prop} {s : β → β → Prop}
    (F : α → β) (hF : ∀ a b, r a b → s (F a) (F b))
    {a b : α} (h : Relation.EqvGen r a b) : Relation.EqvGen s (F a) (F b) := by
  induction h with
  | rel a b h => exact .rel _ _ (hF a b h)
  | refl a => exact .refl _
  | symm a b h ih => exact .symm _ _ ih
  | trans a b c h k ih ik => exact .trans _ _ _ ih ik

private theorem finite_pointwise {α : Type _} {r : α → α → Prop}
    (hr : ∀ a, r a a) (n : ℕ) {σ τ : Fin n → α}
    (h : ∀ i, Relation.EqvGen r (σ i) (τ i)) :
    Relation.EqvGen (fun σ τ : Fin n → α => ∀ i, r (σ i) (τ i)) σ τ := by
  induction n with
  | zero =>
    have he : σ = τ := funext (fun i => Fin.elim0 i)
    subst he
    exact .refl _
  | succ n ih =>
    show Relation.EqvGen (fun σ τ : Fin (n+1) → α => ∀ i, r (σ i) (τ i)) σ τ
    have ht : Relation.EqvGen (fun σ τ : Fin n → α => ∀ i, r (σ i) (τ i))
        (Fin.tail σ) (Fin.tail τ) := ih (fun i => h i.succ)
    have htail : Relation.EqvGen (fun σ τ : Fin (n+1) → α => ∀ i, r (σ i) (τ i))
        (Fin.cons (σ 0) (Fin.tail σ)) (Fin.cons (σ 0) (Fin.tail τ)) := by
      apply eqv_map (r := fun a b : Fin n → α => ∀ i, r (a i) (b i))
        (s := fun a b : Fin (n+1) → α => ∀ i, r (a i) (b i))
        (fun tail : Fin n → α => (Fin.cons (σ 0) tail : Fin (n+1) → α)) ?_ ht
      intro a b hab i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact hr _
      · exact hab j
    have hhead : Relation.EqvGen (fun σ τ : Fin (n+1) → α => ∀ i, r (σ i) (τ i))
        (Fin.cons (σ 0) (Fin.tail τ)) (Fin.cons (τ 0) (Fin.tail τ)) := by
      apply eqv_map (fun a => Fin.cons a (Fin.tail τ)) ?_ (h 0)
      intro a b hab i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact hab
      · exact hr _
    simpa only [Fin.cons_self_tail] using Relation.EqvGen.trans _ _ _ htail hhead

theorem convertible_subst_right {n m : ℕ} (t : Term n) {σ τ : Fin n → Term m}
    (h : ∀ i, LinearJ.Convertible (σ i) (τ i)) :
    LinearJ.Convertible (t.subst σ) (t.subst τ) :=
  eqv_map (fun σ => t.subst σ) (fun _ _ h => (LinearJ.Parallel.rfl t).subst h)
    (finite_pointwise LinearJ.Parallel.rfl n h)

theorem convertible_subst {n m : ℕ} {t u : Term n} (h : LinearJ.Convertible t u)
    {σ τ : Fin n → Term m} (hσ : ∀ i, LinearJ.Convertible (σ i) (τ i)) :
    LinearJ.Convertible (t.subst σ) (u.subst τ) :=
  .trans _ _ _ (conv_map (fun t => t.subst σ)
    (fun h => h.subst (fun i => LinearJ.Parallel.rfl (σ i))) h)
    (convertible_subst_right u hσ)

theorem eval_congr {n m : ℕ} (t : Term n) {ρ τ : Environment n m}
    (h : ∀ i, ρ i = τ i) : eval t ρ = eval t τ := by
  apply ofTerm_eq_iff.mpr
  apply convertible_subst_right
  intro i
  exact ofTerm_eq_iff.mp ((of_rep (ρ i)).trans ((h i).trans (of_rep (τ i)).symm))

theorem eval_var {n m : ℕ} (i : Fin n) (ρ : Environment n m) : eval (.var i) ρ = ρ i :=
  of_rep (ρ i)

theorem eval_conversion {n m : ℕ} {t u : Term n} (h : LinearJ.Convertible t u)
    (ρ : Environment n m) : eval t ρ = eval u ρ :=
  ofTerm_eq_iff.mpr (convertible_subst h (fun _ => .refl _))

theorem qsubst_ofTerm {n m : ℕ} (t : Term n) (ρ : Environment n m) :
    qsubst (ofTerm t) ρ = eval t ρ :=
  eval_conversion (ofTerm_eq_iff.mp (of_rep (ofTerm t))) ρ

theorem eval_subst {n m k : ℕ} (t : Term n) (σ : Fin n → Term m) (ρ : Environment m k) :
    eval (t.subst σ) ρ = eval t (fun i => eval (σ i) ρ) := by
  unfold eval
  rw [Term.subst_comp]
  apply ofTerm_eq_iff.mpr
  apply convertible_subst_right
  intro i
  exact ofTerm_eq_iff.mp (of_rep (ofTerm ((σ i).subst (fun j => rep (ρ j))))).symm

theorem eval_qsubst {n m k : ℕ} (t : Term n) (ρ : Environment n m) (τ : Environment m k) :
    qsubst (eval t ρ) τ = eval t (fun i => qsubst (ρ i) τ) := by
  rw [eval, qsubst_ofTerm, eval_subst]
  rfl

theorem qsubst_comp {n m k : ℕ} (q : Value n) (ρ : Environment n m) (τ : Environment m k) :
    qsubst (qsubst q ρ) τ = qsubst q (fun i => qsubst (ρ i) τ) :=
  eval_qsubst (rep q) ρ τ

theorem eval_identity {n : ℕ} (t : Term n) : eval t (variableEnv n) = ofTerm t := by
  apply ofTerm_eq_iff.mpr
  have hc : LinearJ.Convertible (t.subst (fun i => rep (ofTerm (.var i)))) (t.subst Term.var) :=
    convertible_subst_right t (fun i => ofTerm_eq_iff.mp (of_rep (ofTerm (.var i))))
  simpa only [Term.subst_var, variableEnv] using hc

theorem qsubst_identity {n : ℕ} (q : Value n) : qsubst q (variableEnv n) = q :=
  (eval_identity (rep q)).trans (of_rep q)

theorem qrename_ofTerm {n m : ℕ} (t : Term n) (r : Fin n → Fin m) :
    qrename (ofTerm t) r = ofTerm (t.rename r) :=
  ofTerm_eq_iff.mpr (conv_map (fun t => t.rename r) (fun h => h.rename r)
    (ofTerm_eq_iff.mp (of_rep (ofTerm t))))

theorem qrename_eval {n m k : ℕ} (t : Term n) (ρ : Environment n m) (r : Fin m → Fin k) :
    qrename (eval t ρ) r = eval t (fun i => qrename (ρ i) r) := by
  rw [eval, qrename_ofTerm, Term.rename_subst]
  apply ofTerm_eq_iff.mpr
  apply convertible_subst_right
  intro i
  exact ofTerm_eq_iff.mp (of_rep (ofTerm ((rep (ρ i)).rename r))).symm

theorem eval_rename {n m k : ℕ} (t : Term n) (r : Fin n → Fin m) (ρ : Environment m k) :
    eval (t.rename r) ρ = eval t (ρ ∘ r) := by
  unfold eval
  rw [Term.subst_rename]
  rfl

theorem eval_lift {n m : ℕ} (t : Term (n+1)) (ρ : Environment n m) :
    eval t (liftEnv ρ) = ofTerm (t.subst (Term.upSub (fun i => rep (ρ i)))) := by
  apply ofTerm_eq_iff.mpr
  apply convertible_subst_right
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact ofTerm_eq_iff.mp (of_rep (ofTerm (.var 0)))
  · exact ofTerm_eq_iff.mp (of_rep (qrename (ρ j) Fin.succ))

theorem eval_instantiate {n m : ℕ} (B : Term (n+1)) (a : Term n) (ρ : Environment n m) :
    eval (B.instantiate a) ρ = eval B (Fin.cons (eval a ρ) ρ) := by
  rw [Term.instantiate, eval_subst]
  apply eval_congr
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · exact eval_var j ρ

theorem ofTerm_pi {n : ℕ} (A : Term n) (B : Term (n+1)) :
    pi (ofTerm A) (ofTerm B) = ofTerm (.pi A B) :=
  ofTerm_eq_iff.mpr (conv₂ Term.pi (fun h k => .pi h k)
    (ofTerm_eq_iff.mp (of_rep (ofTerm A))) (ofTerm_eq_iff.mp (of_rep (ofTerm B))))

theorem ofTerm_sigma {n : ℕ} (A : Term n) (B : Term (n+1)) :
    sigma (ofTerm A) (ofTerm B) = ofTerm (.sigma A B) :=
  ofTerm_eq_iff.mpr (conv₂ Term.sigma (fun h k => .sigma h k)
    (ofTerm_eq_iff.mp (of_rep (ofTerm A))) (ofTerm_eq_iff.mp (of_rep (ofTerm B))))

theorem ofTerm_app {n : ℕ} (f a : Term n) :
    app (ofTerm f) (ofTerm a) = ofTerm (.app f a) :=
  ofTerm_eq_iff.mpr (conv₂ Term.app (fun h k => .app h k)
    (ofTerm_eq_iff.mp (of_rep (ofTerm f))) (ofTerm_eq_iff.mp (of_rep (ofTerm a))))

theorem ofTerm_pair {n : ℕ} (a b : Term n) :
    pair (ofTerm a) (ofTerm b) = ofTerm (.pair a b) :=
  ofTerm_eq_iff.mpr (conv₂ Term.pair (fun h k => .pair h k)
    (ofTerm_eq_iff.mp (of_rep (ofTerm a))) (ofTerm_eq_iff.mp (of_rep (ofTerm b))))

theorem ofTerm_refl {n : ℕ} (a : Term n) : refl (ofTerm a) = ofTerm (.refl a) :=
  ofTerm_eq_iff.mpr (conv_map Term.refl (fun h => .refl h)
    (ofTerm_eq_iff.mp (of_rep (ofTerm a))))

theorem ofTerm_instantiate {n : ℕ} (B : Term (n+1)) (a : Term n) :
    instantiate (ofTerm B) (ofTerm a) = ofTerm (B.instantiate a) :=
  ofTerm_eq_iff.mpr (conv₂ Term.instantiate (fun h k => h.instantiate k)
    (ofTerm_eq_iff.mp (of_rep (ofTerm B))) (ofTerm_eq_iff.mp (of_rep (ofTerm a))))

theorem eval_pi {n m : ℕ} (A : Term n) (B : Term (n+1)) (ρ : Environment n m) :
    eval (.pi A B) ρ = pi (eval A ρ) (eval B (liftEnv ρ)) := by
  rw [eval_lift]
  exact (ofTerm_pi _ _).symm

theorem eval_sigma {n m : ℕ} (A : Term n) (B : Term (n+1)) (ρ : Environment n m) :
    eval (.sigma A B) ρ = sigma (eval A ρ) (eval B (liftEnv ρ)) := by
  rw [eval_lift]
  exact (ofTerm_sigma _ _).symm

theorem eval_app {n m : ℕ} (f a : Term n) (ρ : Environment n m) :
    eval (.app f a) ρ = app (eval f ρ) (eval a ρ) := (ofTerm_app _ _).symm

theorem eval_pair {n m : ℕ} (a b : Term n) (ρ : Environment n m) :
    eval (.pair a b) ρ = pair (eval a ρ) (eval b ρ) := (ofTerm_pair _ _).symm

theorem eval_refl {n m : ℕ} (a : Term n) (ρ : Environment n m) :
    eval (.refl a) ρ = refl (eval a ρ) := (ofTerm_refl _).symm

theorem subst_up_instantiate {n m : ℕ} (B : Term (n+1)) (σ : Fin n → Term m) (a : Term m) :
    (B.subst (Term.upSub σ)).instantiate a = B.subst (Fin.cons a σ) := by
  simp only [Term.instantiate, Term.subst_comp]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · exact Term.instantiate_weaken (σ j) a

theorem instantiate_eval_lift {n m : ℕ} (B : Term (n+1)) (ρ : Environment n m) (a : Value m) :
    instantiate (eval B (liftEnv ρ)) a = eval B (Fin.cons a ρ) := by
  rw [eval_lift, ← of_rep a, ofTerm_instantiate, subst_up_instantiate]
  apply ofTerm_eq_iff.mpr
  apply convertible_subst_right
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact ofTerm_eq_iff.mp (of_rep (ofTerm (rep a))).symm
  · exact .refl _

theorem eval_lam_app {n m : ℕ} (A : Term n) (b : Term (n+1))
    (ρ : Environment n m) (a : Value m) :
    app (eval (.lam A b) ρ) a = eval b (Fin.cons a ρ) := by
  rw [← of_rep a]
  change app (ofTerm _) (ofTerm (rep a)) = _
  rw [ofTerm_app]
  calc
    _ = ofTerm ((b.subst (Term.upSub (fun i => rep (ρ i)))).instantiate (rep a)) :=
      ofTerm_eq_iff.mpr (.rel _ _ (LinearJ.Parallel.beta
        (LinearJ.Parallel.rfl _) (LinearJ.Parallel.rfl _)))
    _ = instantiate (eval b (liftEnv ρ)) (ofTerm (rep a)) := by
      rw [eval_lift, ofTerm_instantiate]
    _ = _ := instantiate_eval_lift _ _ _

theorem ofTerm_id {n : ℕ} (A a b : Term n) :
    id (ofTerm A) (ofTerm a) (ofTerm b) = ofTerm (.id A a b) := by
  apply ofTerm_eq_iff.mpr
  exact .trans _ _ _
    (conv_map (fun X => Term.id X (rep (ofTerm a)) (rep (ofTerm b)))
      (fun h => .id h (.rfl _) (.rfl _)) (ofTerm_eq_iff.mp (of_rep (ofTerm A))))
    (conv₂ (Term.id A) (fun h k => .id (.rfl _) h k)
      (ofTerm_eq_iff.mp (of_rep (ofTerm a)))
      (ofTerm_eq_iff.mp (of_rep (ofTerm b))))

theorem eval_id {n m : ℕ} (A a b : Term n) (ρ : Environment n m) :
    eval (.id A a b) ρ = id (eval A ρ) (eval a ρ) (eval b ρ) :=
  (ofTerm_id _ _ _).symm

end Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRealizabilityEnvironment
