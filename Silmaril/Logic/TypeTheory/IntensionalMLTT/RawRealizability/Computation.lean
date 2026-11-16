module

public import Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRealizabilityComputation

public section

/-! Computation of projections and eliminators in the LinearJ quotient target. -/

namespace Silmaril.Logic.TypeTheory.IntensionalMLTT.RawRealizability

theorem eval_fst_realizer {n m : ℕ} (p : Term n) (ρ : Environment n m)
    (a b : Value m) (hp : eval p ρ = pair a b) : eval (.fst p) ρ = a :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRealizabilityComputation.eval_fst_realizer p ρ a b hp

theorem eval_snd_realizer {n m : ℕ} (p : Term n) (ρ : Environment n m)
    (a b : Value m) (hp : eval p ρ = pair a b) : eval (.snd p) ρ = b :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRealizabilityComputation.eval_snd_realizer p ρ a b hp

theorem eval_natrec_zero {n m : ℕ} (C : Term (n+1)) (z s t : Term n)
    (ρ : Environment n m) (ht : eval t ρ = ofTerm .zero) :
    eval (.natrec C z s t) ρ = eval z ρ :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRealizabilityComputation.eval_natrec_zero C z s t ρ ht

theorem eval_j_refl {n m : ℕ} (A a d b p : Term n) (C : Term (n+2))
    (ρ : Environment n m) (c : Value m) (hp : eval p ρ = refl c) :
    eval (.j A a C d b p) ρ = eval d ρ :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRealizabilityComputation.eval_j_refl A a d b p C ρ c hp

theorem eval_natrec_succ {n m : ℕ} (C : Term (n+1)) (z s t : Term n)
    (ρ : Environment n m) (u : Term m) (ht : eval t ρ = ofTerm (.succ u)) :
    eval (.natrec C z s t) ρ =
      app (app (eval s ρ) (ofTerm u))
        (ofTerm (.natrec (C.subst (Term.upSub (fun i => rep (ρ i))))
          (z.subst (fun i => rep (ρ i))) (s.subst (fun i => rep (ρ i))) u)) :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRealizabilityComputation.eval_natrec_succ C z s t ρ u ht

theorem eval_weaken {n m : ℕ} (t : Term n) (ρ : Environment n m) (a : Value m) :
    eval t.weaken (Fin.cons a ρ) = eval t ρ :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRealizabilityComputation.eval_weaken t ρ a

theorem eval_natStep_body {n m : ℕ} (C : Term (n+1)) (ρ : Environment n m)
    (t r : Value m) :
    eval (C.subst (Fin.cons (.succ (.var 1)) (fun i => .var i.succ.succ)))
      (Fin.cons r (Fin.cons t ρ)) = eval C (Fin.cons (ofTerm (.succ (rep t))) ρ) :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRealizabilityComputation.eval_natStep_body C ρ t r

theorem eval_instantiate₂ {n m : ℕ} (C : Term (n+2)) (a p : Term n)
    (ρ : Environment n m) :
    eval (C.instantiate₂ a p) ρ = eval C (Fin.cons (eval p ρ) (Fin.cons (eval a ρ) ρ)) :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRealizabilityComputation.eval_instantiate₂ C a p ρ

theorem eval_succ_of_nat {n : ℕ} (t : Term n) (ρ : Environment n 0) (k : ℕ)
    (ht : eval t ρ = ofTerm (numeral k)) :
    eval (.succ t) ρ = ofTerm (numeral (k+1)) :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRealizabilityComputation.eval_succ_of_nat t ρ k ht

theorem succ_rep_numeral (k : ℕ) :
    ofTerm (.succ (rep (ofTerm (numeral k)))) = ofTerm (numeral (k+1)) :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRealizabilityComputation.succ_rep_numeral k

theorem eval_natrec_realizer {n m : ℕ} (C : Term (n+1)) (z s t : Term n)
    (ρ : Environment n m) (u : Term m) (ht : eval t ρ = ofTerm u) :
    eval (.natrec C z s t) ρ =
      ofTerm (.natrec (C.subst (Term.upSub (fun i => rep (ρ i))))
        (z.subst (fun i => rep (ρ i))) (s.subst (fun i => rep (ρ i))) u) :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRealizabilityComputation.eval_natrec_realizer C z s t ρ u ht

theorem ofTerm_natrec_zero {n : ℕ} (C : Term (n+1)) (z s : Term n) :
    ofTerm (.natrec C z s .zero) = ofTerm z :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRealizabilityComputation.ofTerm_natrec_zero C z s

theorem ofTerm_natrec_succ {n : ℕ} (C : Term (n+1)) (z s t : Term n) :
    ofTerm (.natrec C z s (.succ t)) =
      app (app (ofTerm s) (ofTerm t)) (ofTerm (.natrec C z s t)) :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRealizabilityComputation.ofTerm_natrec_succ C z s t

end Silmaril.Logic.TypeTheory.IntensionalMLTT.RawRealizability
