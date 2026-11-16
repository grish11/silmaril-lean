module

public import Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRealizabilityEnvironment

@[expose] public section

/-! Quotient evaluation respects substitution, conversion and binding. -/

namespace Silmaril.Logic.TypeTheory.IntensionalMLTT.RawRealizability

theorem convertible_subst_right {n m : ℕ} (t : Term n) {σ τ : Fin n → Term m}
    (h : ∀ i, LinearJ.Convertible (σ i) (τ i)) :
    LinearJ.Convertible (t.subst σ) (t.subst τ) :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRealizabilityEnvironment.convertible_subst_right t h

theorem convertible_subst {n m : ℕ} {t u : Term n} (h : LinearJ.Convertible t u)
    {σ τ : Fin n → Term m} (hσ : ∀ i, LinearJ.Convertible (σ i) (τ i)) :
    LinearJ.Convertible (t.subst σ) (u.subst τ) :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRealizabilityEnvironment.convertible_subst h hσ

theorem eval_congr {n m : ℕ} (t : Term n) {ρ τ : Environment n m}
    (h : ∀ i, ρ i = τ i) : eval t ρ = eval t τ :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRealizabilityEnvironment.eval_congr t h

theorem eval_var {n m : ℕ} (i : Fin n) (ρ : Environment n m) : eval (.var i) ρ = ρ i :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRealizabilityEnvironment.eval_var i ρ

theorem eval_conversion {n m : ℕ} {t u : Term n} (h : LinearJ.Convertible t u)
    (ρ : Environment n m) : eval t ρ = eval u ρ :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRealizabilityEnvironment.eval_conversion h ρ

theorem qsubst_ofTerm {n m : ℕ} (t : Term n) (ρ : Environment n m) :
    qsubst (ofTerm t) ρ = eval t ρ :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRealizabilityEnvironment.qsubst_ofTerm t ρ

theorem eval_subst {n m k : ℕ} (t : Term n) (σ : Fin n → Term m) (ρ : Environment m k) :
    eval (t.subst σ) ρ = eval t (fun i => eval (σ i) ρ) :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRealizabilityEnvironment.eval_subst t σ ρ

theorem eval_qsubst {n m k : ℕ} (t : Term n) (ρ : Environment n m) (τ : Environment m k) :
    qsubst (eval t ρ) τ = eval t (fun i => qsubst (ρ i) τ) :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRealizabilityEnvironment.eval_qsubst t ρ τ

theorem qsubst_comp {n m k : ℕ} (q : Value n) (ρ : Environment n m) (τ : Environment m k) :
    qsubst (qsubst q ρ) τ = qsubst q (fun i => qsubst (ρ i) τ) :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRealizabilityEnvironment.qsubst_comp q ρ τ

theorem eval_identity {n : ℕ} (t : Term n) : eval t (variableEnv n) = ofTerm t :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRealizabilityEnvironment.eval_identity t

theorem qsubst_identity {n : ℕ} (q : Value n) : qsubst q (variableEnv n) = q :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRealizabilityEnvironment.qsubst_identity q

theorem qrename_ofTerm {n m : ℕ} (t : Term n) (r : Fin n → Fin m) :
    qrename (ofTerm t) r = ofTerm (t.rename r) :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRealizabilityEnvironment.qrename_ofTerm t r

theorem qrename_eval {n m k : ℕ} (t : Term n) (ρ : Environment n m) (r : Fin m → Fin k) :
    qrename (eval t ρ) r = eval t (fun i => qrename (ρ i) r) :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRealizabilityEnvironment.qrename_eval t ρ r

theorem eval_rename {n m k : ℕ} (t : Term n) (r : Fin n → Fin m) (ρ : Environment m k) :
    eval (t.rename r) ρ = eval t (ρ ∘ r) :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRealizabilityEnvironment.eval_rename t r ρ

theorem eval_lift {n m : ℕ} (t : Term (n+1)) (ρ : Environment n m) :
    eval t (liftEnv ρ) = ofTerm (t.subst (Term.upSub (fun i => rep (ρ i)))) :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRealizabilityEnvironment.eval_lift t ρ

theorem eval_instantiate {n m : ℕ} (B : Term (n+1)) (a : Term n) (ρ : Environment n m) :
    eval (B.instantiate a) ρ = eval B (Fin.cons (eval a ρ) ρ) :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRealizabilityEnvironment.eval_instantiate B a ρ

theorem ofTerm_pi {n : ℕ} (A : Term n) (B : Term (n+1)) :
    pi (ofTerm A) (ofTerm B) = ofTerm (.pi A B) :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRealizabilityEnvironment.ofTerm_pi A B

theorem ofTerm_sigma {n : ℕ} (A : Term n) (B : Term (n+1)) :
    sigma (ofTerm A) (ofTerm B) = ofTerm (.sigma A B) :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRealizabilityEnvironment.ofTerm_sigma A B

theorem ofTerm_app {n : ℕ} (f a : Term n) :
    app (ofTerm f) (ofTerm a) = ofTerm (.app f a) :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRealizabilityEnvironment.ofTerm_app f a

theorem ofTerm_pair {n : ℕ} (a b : Term n) :
    pair (ofTerm a) (ofTerm b) = ofTerm (.pair a b) :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRealizabilityEnvironment.ofTerm_pair a b

theorem ofTerm_refl {n : ℕ} (a : Term n) : refl (ofTerm a) = ofTerm (.refl a) :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRealizabilityEnvironment.ofTerm_refl a

theorem ofTerm_instantiate {n : ℕ} (B : Term (n+1)) (a : Term n) :
    instantiate (ofTerm B) (ofTerm a) = ofTerm (B.instantiate a) :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRealizabilityEnvironment.ofTerm_instantiate B a

theorem eval_pi {n m : ℕ} (A : Term n) (B : Term (n+1)) (ρ : Environment n m) :
    eval (.pi A B) ρ = pi (eval A ρ) (eval B (liftEnv ρ)) :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRealizabilityEnvironment.eval_pi A B ρ

theorem eval_sigma {n m : ℕ} (A : Term n) (B : Term (n+1)) (ρ : Environment n m) :
    eval (.sigma A B) ρ = sigma (eval A ρ) (eval B (liftEnv ρ)) :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRealizabilityEnvironment.eval_sigma A B ρ

theorem eval_app {n m : ℕ} (f a : Term n) (ρ : Environment n m) :
    eval (.app f a) ρ = app (eval f ρ) (eval a ρ) :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRealizabilityEnvironment.eval_app f a ρ

theorem eval_pair {n m : ℕ} (a b : Term n) (ρ : Environment n m) :
    eval (.pair a b) ρ = pair (eval a ρ) (eval b ρ) :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRealizabilityEnvironment.eval_pair a b ρ

theorem eval_refl {n m : ℕ} (a : Term n) (ρ : Environment n m) :
    eval (.refl a) ρ = refl (eval a ρ) :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRealizabilityEnvironment.eval_refl a ρ

theorem subst_up_instantiate {n m : ℕ} (B : Term (n+1)) (σ : Fin n → Term m) (a : Term m) :
    (B.subst (Term.upSub σ)).instantiate a = B.subst (Fin.cons a σ) :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRealizabilityEnvironment.subst_up_instantiate B σ a

theorem instantiate_eval_lift {n m : ℕ} (B : Term (n+1)) (ρ : Environment n m) (a : Value m) :
    instantiate (eval B (liftEnv ρ)) a = eval B (Fin.cons a ρ) :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRealizabilityEnvironment.instantiate_eval_lift B ρ a

theorem eval_lam_app {n m : ℕ} (A : Term n) (b : Term (n+1))
    (ρ : Environment n m) (a : Value m) :
    app (eval (.lam A b) ρ) a = eval b (Fin.cons a ρ) :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRealizabilityEnvironment.eval_lam_app A b ρ a

theorem ofTerm_id {n : ℕ} (A a b : Term n) :
    id (ofTerm A) (ofTerm a) (ofTerm b) = ofTerm (.id A a b) :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRealizabilityEnvironment.ofTerm_id A a b

theorem eval_id {n m : ℕ} (A a b : Term n) (ρ : Environment n m) :
    eval (.id A a b) ρ = id (eval A ρ) (eval a ρ) (eval b ρ) :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRealizabilityEnvironment.eval_id A a b ρ

end Silmaril.Logic.TypeTheory.IntensionalMLTT.RawRealizability
