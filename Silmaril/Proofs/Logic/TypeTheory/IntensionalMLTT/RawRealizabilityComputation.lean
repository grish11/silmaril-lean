module

public import Silmaril.Logic.TypeTheory.IntensionalMLTT.RawRealizability.Environment
public section

open Silmaril.Logic.TypeTheory.IntensionalMLTT
open Silmaril.Logic.TypeTheory.IntensionalMLTT.RawRealizability

namespace Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRealizabilityComputation

theorem eval_fst_realizer {n m : ℕ} (p : Term n) (ρ : Environment n m)
    (a b : Value m) (hp : eval p ρ = pair a b) : eval (.fst p) ρ = a := by
  have h := ofTerm_eq_iff.mp hp
  have hfst := conv_map Term.fst (fun h => .fst h) h
  exact (ofTerm_eq_iff.mpr (.trans _ _ _ hfst
    (.rel _ _ (LinearJ.Parallel.fst_pair (.rfl _))))).trans (of_rep a)

theorem eval_snd_realizer {n m : ℕ} (p : Term n) (ρ : Environment n m)
    (a b : Value m) (hp : eval p ρ = pair a b) : eval (.snd p) ρ = b := by
  have h := ofTerm_eq_iff.mp hp
  have hsnd := conv_map Term.snd (fun h => .snd h) h
  exact (ofTerm_eq_iff.mpr (.trans _ _ _ hsnd
    (.rel _ _ (LinearJ.Parallel.snd_pair (.rfl _))))).trans (of_rep b)

theorem eval_natrec_zero {n m : ℕ} (C : Term (n+1)) (z s t : Term n)
    (ρ : Environment n m) (ht : eval t ρ = ofTerm .zero) :
    eval (.natrec C z s t) ρ = eval z ρ := by
  have h := ofTerm_eq_iff.mp ht
  apply ofTerm_eq_iff.mpr
  exact .trans _ _ _ (conv_map (fun t => Term.natrec _ _ _ t)
    (fun h => .natrec (.rfl _) (.rfl _) (.rfl _) h) h)
    (.rel _ _ (LinearJ.Parallel.nat_zero (.rfl _)))

theorem eval_j_refl {n m : ℕ} (A a d b p : Term n) (C : Term (n+2))
    (ρ : Environment n m) (c : Value m) (hp : eval p ρ = refl c) :
    eval (.j A a C d b p) ρ = eval d ρ := by
  have h := ofTerm_eq_iff.mp hp
  apply ofTerm_eq_iff.mpr
  exact .trans _ _ _ (conv_map (fun p => Term.j _ _ _ _ _ p)
    (fun h => .j (.rfl _) (.rfl _) (.rfl _) (.rfl _) (.rfl _) h) h)
    (.rel _ _ (LinearJ.Parallel.j_refl (.rfl _)))

theorem eval_natrec_succ {n m : ℕ} (C : Term (n+1)) (z s t : Term n)
    (ρ : Environment n m) (u : Term m) (ht : eval t ρ = ofTerm (.succ u)) :
    eval (.natrec C z s t) ρ =
      app (app (eval s ρ) (ofTerm u))
        (ofTerm (.natrec (C.subst (Term.upSub (fun i => rep (ρ i))))
          (z.subst (fun i => rep (ρ i))) (s.subst (fun i => rep (ρ i))) u)) := by
  change _ = app (app (ofTerm _) (ofTerm u)) (ofTerm _)
  rw [ofTerm_app, ofTerm_app]
  apply ofTerm_eq_iff.mpr
  have h := ofTerm_eq_iff.mp ht
  exact .trans _ _ _ (conv_map (fun t => Term.natrec _ _ _ t)
    (fun h => .natrec (.rfl _) (.rfl _) (.rfl _) h) h)
    (.rel _ _ (LinearJ.Parallel.nat_succ (.rfl _) (.rfl _) (.rfl _) (.rfl _)))
theorem eval_weaken {n m : ℕ} (t : Term n) (ρ : Environment n m) (a : Value m) :
    eval t.weaken (Fin.cons a ρ) = eval t ρ := by
  rw [Term.weaken, eval_rename]
  rfl

theorem eval_natStep_body {n m : ℕ} (C : Term (n+1)) (ρ : Environment n m)
    (t r : Value m) :
    eval (C.subst (Fin.cons (.succ (.var 1)) (fun i => .var i.succ.succ)))
      (Fin.cons r (Fin.cons t ρ)) = eval C (Fin.cons (ofTerm (.succ (rep t))) ρ) := by
  rw [eval_subst]
  apply eval_congr
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · exact eval_var _ _

theorem eval_instantiate₂ {n m : ℕ} (C : Term (n+2)) (a p : Term n)
    (ρ : Environment n m) :
    eval (C.instantiate₂ a p) ρ = eval C (Fin.cons (eval p ρ) (Fin.cons (eval a ρ) ρ)) := by
  rw [Term.instantiate₂, eval_subst]
  apply eval_congr
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · refine Fin.cases ?_ (fun k => ?_) j
    · rfl
    · exact eval_var _ _

theorem eval_succ_of_nat {n : ℕ} (t : Term n) (ρ : Environment n 0) (k : ℕ)
    (ht : eval t ρ = ofTerm (numeral k)) :
    eval (.succ t) ρ = ofTerm (numeral (k+1)) :=
  ofTerm_eq_iff.mpr (conv_map Term.succ (fun h => .succ h) (ofTerm_eq_iff.mp ht))

theorem succ_rep_numeral (k : ℕ) :
    ofTerm (.succ (rep (ofTerm (numeral k)))) = ofTerm (numeral (k+1)) :=
  ofTerm_eq_iff.mpr (conv_map Term.succ (fun h => .succ h)
    (ofTerm_eq_iff.mp (of_rep (ofTerm (numeral k)))))

theorem eval_natrec_realizer {n m : ℕ} (C : Term (n+1)) (z s t : Term n)
    (ρ : Environment n m) (u : Term m) (ht : eval t ρ = ofTerm u) :
    eval (.natrec C z s t) ρ =
      ofTerm (.natrec (C.subst (Term.upSub (fun i => rep (ρ i))))
        (z.subst (fun i => rep (ρ i))) (s.subst (fun i => rep (ρ i))) u) :=
  ofTerm_eq_iff.mpr (conv_map (fun t => Term.natrec _ _ _ t)
    (fun h => .natrec (.rfl _) (.rfl _) (.rfl _) h) (ofTerm_eq_iff.mp ht))

theorem ofTerm_natrec_zero {n : ℕ} (C : Term (n+1)) (z s : Term n) :
    ofTerm (.natrec C z s .zero) = ofTerm z :=
  ofTerm_eq_iff.mpr (.rel _ _ (LinearJ.Parallel.nat_zero (.rfl _)))

theorem ofTerm_natrec_succ {n : ℕ} (C : Term (n+1)) (z s t : Term n) :
    ofTerm (.natrec C z s (.succ t)) =
      app (app (ofTerm s) (ofTerm t)) (ofTerm (.natrec C z s t)) := by
  rw [ofTerm_app, ofTerm_app]
  exact ofTerm_eq_iff.mpr (.rel _ _
    (LinearJ.Parallel.nat_succ (.rfl _) (.rfl _) (.rfl _) (.rfl _)))

end Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.RawRealizabilityComputation
