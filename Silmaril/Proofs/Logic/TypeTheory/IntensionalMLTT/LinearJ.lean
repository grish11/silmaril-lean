module

public import Silmaril.Logic.TypeTheory.IntensionalMLTT.LinearJ.Defs

@[expose] public section

namespace Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.LinearJ

open Silmaril.Logic.TypeTheory.IntensionalMLTT
open Silmaril.Logic.TypeTheory.IntensionalMLTT.LinearJ

theorem Parallel.rfl {n : ℕ} (t : Term n) : Parallel t t := by
  induction t with
  | var i => exact .var i
  | univ i => exact .univ i
  | empty  => exact .empty 
  | unit  => exact .unit 
  | star  => exact .star 
  | nat  => exact .nat 
  | zero  => exact .zero 
  | succ t iht => exact .succ iht
  | pi A B ihA ihB => exact .pi ihA ihB
  | sigma A B ihA ihB => exact .sigma ihA ihB
  | lam A body ihA ihbody => exact .lam ihA ihbody
  | app f a ihf iha => exact .app ihf iha
  | pair a b iha ihb => exact .pair iha ihb
  | fst p ihp => exact .fst ihp
  | snd p ihp => exact .snd ihp
  | natrec C z s t ihC ihz ihs iht => exact .natrec ihC ihz ihs iht
  | absurd A e ihA ihe => exact .absurd ihA ihe
  | id A a b ihA iha ihb => exact .id ihA iha ihb
  | refl a iha => exact .refl iha
  | j A a C d b p ihA iha ihC ihd ihb ihp => exact .j ihA iha ihC ihd ihb ihp

private theorem rename_instantiate {n m : ℕ} (t : Term (n + 1)) (a : Term n)
    (ρ : Fin n → Fin m) :
    (t.instantiate a).rename ρ = (t.rename (Term.upRen ρ)).instantiate (a.rename ρ) := by
  simp only [Term.instantiate, Term.rename_subst, Term.subst_rename]
  congr 1
  funext i
  cases i using Fin.cases <;> rfl

private theorem subst_instantiate {n m : ℕ} (t : Term (n + 1)) (a : Term n)
    (σ : Fin n → Term m) :
    (t.instantiate a).subst σ = (t.subst (Term.upSub σ)).instantiate (a.subst σ) := by
  simp only [Term.instantiate, Term.subst_comp]
  congr 1
  funext i
  cases i using Fin.cases with
  | zero => rfl
  | succ i => exact (Term.instantiate_weaken (σ i) (a.subst σ)).symm

theorem Parallel.rename {n : ℕ} {t u : Term n} (h : Parallel t u)
    {m : ℕ} (ρ : Fin n → Fin m) : Parallel (t.rename ρ) (u.rename ρ) := by
  induction h generalizing m with
  | var i => exact .var  (ρ i)
  | univ i => exact .univ i
  | empty  => exact .empty 
  | unit  => exact .unit 
  | star  => exact .star 
  | nat  => exact .nat 
  | zero  => exact .zero 
  | succ ht iht => exact .succ (iht ρ)
  | pi hA hB ihA ihB => exact .pi (ihA ρ) (ihB (Term.upRen ρ))
  | sigma hA hB ihA ihB => exact .sigma (ihA ρ) (ihB (Term.upRen ρ))
  | lam hA hbody ihA ihbody => exact .lam (ihA ρ) (ihbody (Term.upRen ρ))
  | app hf ha ihf iha => exact .app (ihf ρ) (iha ρ)
  | pair ha hb iha ihb => exact .pair (iha ρ) (ihb ρ)
  | fst hp ihp => exact .fst (ihp ρ)
  | snd hp ihp => exact .snd (ihp ρ)
  | natrec hC hz hs ht ihC ihz ihs iht => exact .natrec (ihC (Term.upRen ρ)) (ihz ρ) (ihs ρ) (iht ρ)
  | absurd hA he ihA ihe => exact .absurd (ihA ρ) (ihe ρ)
  | id hA ha hb ihA iha ihb => exact .id (ihA ρ) (iha ρ) (ihb ρ)
  | refl ha iha => exact .refl (iha ρ)
  | j hA ha hC hd hb hp ihA iha ihC ihd ihb ihp => exact .j (ihA ρ) (iha ρ) (ihC (Term.upRen (Term.upRen ρ))) (ihd ρ) (ihb ρ) (ihp ρ)
  | beta ht ha iht iha => simpa only [Term.rename, rename_instantiate] using Parallel.beta (iht (Term.upRen ρ)) (iha ρ)
  | fst_pair ha ih => exact .fst_pair (ih ρ)
  | snd_pair hb ih => exact .snd_pair (ih ρ)
  | nat_zero hz ih => exact .nat_zero (ih ρ)
  | nat_succ hC hz hs ht ihC ihz ihs iht => exact .nat_succ (ihC (Term.upRen ρ)) (ihz ρ) (ihs ρ) (iht ρ)
  | j_refl hd ih => exact .j_refl (ih ρ)

theorem Parallel.upSub {n m : ℕ} {σ τ : Fin n → Term m}
    (h : ∀ i, Parallel (σ i) (τ i)) (i : Fin (n + 1)) :
    Parallel (Term.upSub σ i) (Term.upSub τ i) := by
  cases i using Fin.cases with
  | zero => exact .var 0
  | succ i => exact Parallel.rename (h i) Fin.succ

theorem Parallel.subst {n : ℕ} {t u : Term n} (h : Parallel t u)
    {m : ℕ} {σ τ : Fin n → Term m} (hσ : ∀ i, Parallel (σ i) (τ i)) :
    Parallel (t.subst σ) (u.subst τ) := by
  induction h generalizing m with
  | var i => exact hσ i
  | univ i => exact .univ i
  | empty  => exact .empty 
  | unit  => exact .unit 
  | star  => exact .star 
  | nat  => exact .nat 
  | zero  => exact .zero 
  | succ ht iht => exact .succ (iht hσ)
  | pi hA hB ihA ihB => exact .pi (ihA hσ) (ihB (Parallel.upSub hσ))
  | sigma hA hB ihA ihB => exact .sigma (ihA hσ) (ihB (Parallel.upSub hσ))
  | lam hA hbody ihA ihbody => exact .lam (ihA hσ) (ihbody (Parallel.upSub hσ))
  | app hf ha ihf iha => exact .app (ihf hσ) (iha hσ)
  | pair ha hb iha ihb => exact .pair (iha hσ) (ihb hσ)
  | fst hp ihp => exact .fst (ihp hσ)
  | snd hp ihp => exact .snd (ihp hσ)
  | natrec hC hz hs ht ihC ihz ihs iht => exact .natrec (ihC (Parallel.upSub hσ)) (ihz hσ) (ihs hσ) (iht hσ)
  | absurd hA he ihA ihe => exact .absurd (ihA hσ) (ihe hσ)
  | id hA ha hb ihA iha ihb => exact .id (ihA hσ) (iha hσ) (ihb hσ)
  | refl ha iha => exact .refl (iha hσ)
  | j hA ha hC hd hb hp ihA iha ihC ihd ihb ihp => exact .j (ihA hσ) (iha hσ) (ihC (Parallel.upSub (Parallel.upSub hσ))) (ihd hσ) (ihb hσ) (ihp hσ)
  | beta ht ha iht iha => simpa only [Term.subst, subst_instantiate] using Parallel.beta (iht (Parallel.upSub hσ)) (iha hσ)
  | fst_pair ha ih => exact .fst_pair (ih hσ)
  | snd_pair hb ih => exact .snd_pair (ih hσ)
  | nat_zero hz ih => exact .nat_zero (ih hσ)
  | nat_succ hC hz hs ht ihC ihz ihs iht => exact .nat_succ (ihC (Parallel.upSub hσ)) (ihz hσ) (ihs hσ) (iht hσ)
  | j_refl hd ih => exact .j_refl (ih hσ)

theorem Parallel.instantiate {n : ℕ} {t u : Term (n + 1)} {a b : Term n}
    (h : Parallel t u) (ha : Parallel a b) : Parallel (t.instantiate a) (u.instantiate b) :=
  Parallel.subst h (Fin.cases ha fun i => Parallel.var i)

theorem Parallel.triangle {n : ℕ} {t u : Term n} (h : Parallel t u) : Parallel u (develop t) := by
  induction h with
  | var i => exact .var i
  | univ i => exact .univ i
  | empty => exact .empty
  | unit => exact .unit
  | star => exact .star
  | nat => exact .nat
  | zero => exact .zero
  | succ ht iht => exact .succ iht
  | pi hA hB ihA ihB => exact .pi ihA ihB
  | sigma hA hB ihA ihB => exact .sigma ihA ihB
  | lam hA ht ihA iht => exact .lam ihA iht
  | @app n f f' a a' hf ha ihf iha =>
    cases f <;> try exact .app ihf iha
    case lam A body =>
      cases hf with
      | lam hA hbody =>
        cases ihf with
        | lam hA' hbody' => exact .beta hbody' iha
  | pair ha hb iha ihb => exact .pair iha ihb
  | @fst n p p' hp ihp =>
    cases p <;> try exact .fst ihp
    case pair a b =>
      cases hp with
      | pair ha hb =>
        cases ihp with
        | pair ha' hb' => exact .fst_pair ha'
  | @snd n p p' hp ihp =>
    cases p <;> try exact .snd ihp
    case pair a b =>
      cases hp with
      | pair ha hb =>
        cases ihp with
        | pair ha' hb' => exact .snd_pair hb'
  | @natrec n C C' z z' s s' t t' hC hz hs ht ihC ihz ihs iht =>
    show Parallel (.natrec C' z' s' t') (develop (.natrec C z s t))
    cases t <;> try exact .natrec ihC ihz ihs iht
    case zero =>
      cases ht
      exact .nat_zero ihz
    case succ t =>
      cases ht with
      | succ ht =>
        cases iht with
        | succ iht => exact .nat_succ ihC ihz ihs iht
  | absurd hA he ihA ihe => exact .absurd ihA ihe
  | id hA ha hb ihA iha ihb => exact .id ihA iha ihb
  | refl ha iha => exact .refl iha
  | @j n A A' a a' C C' d d' b b' p p' hA ha hC hd hb hp ihA iha ihC ihd ihb ihp =>
    cases p <;> try exact .j ihA iha ihC ihd ihb ihp
    case refl c =>
      cases hp
      exact .j_refl ihd
  | beta ht ha iht iha => exact Parallel.instantiate iht iha
  | fst_pair ha iha => exact iha
  | snd_pair hb ihb => exact ihb
  | nat_zero hz ihz => exact ihz
  | nat_succ hC hz hs ht ihC ihz ihs iht =>
    exact .app (.app ihs iht) (.natrec ihC ihz ihs iht)
  | j_refl hd ihd => exact ihd



theorem Parallel.diamond {n : ℕ} {t u v : Term n} (hu : Parallel t u) (hv : Parallel t v) :
    ∃ w, Parallel u w ∧ Parallel v w := ⟨develop t, Parallel.triangle hu, Parallel.triangle hv⟩

theorem confluent {n : ℕ} {t u v : Term n} (hu : Silmaril.Logic.TypeTheory.IntensionalMLTT.LinearJ.Reduces t u) (hv : Silmaril.Logic.TypeTheory.IntensionalMLTT.LinearJ.Reduces t v) :
    Relation.Join (@Silmaril.Logic.TypeTheory.IntensionalMLTT.LinearJ.Reduces n) u v :=
  Relation.church_rosser (fun _ _ _ hu hv =>
    let ⟨w, huw, hvw⟩ := Parallel.diamond hu hv
    ⟨w, .single huw, .single hvw⟩) hu hv

theorem convertible_iff_join {n : ℕ} {t u : Term n} :
    Silmaril.Logic.TypeTheory.IntensionalMLTT.LinearJ.Convertible t u ↔ Relation.Join (@Silmaril.Logic.TypeTheory.IntensionalMLTT.LinearJ.Reduces n) t u := by
  constructor
  · intro h
    induction h with
    | rel t u h => exact ⟨u, .single h, .refl⟩
    | refl t => exact ⟨t, .refl, .refl⟩
    | symm t u h ih =>
      obtain ⟨v, ht, hu⟩ := ih
      exact ⟨v, hu, ht⟩
    | trans t u v h k ih ik =>
      obtain ⟨w, htw, huw⟩ := ih
      obtain ⟨x, hux, hvx⟩ := ik
      obtain ⟨y, hwy, hxy⟩ := confluent huw hux
      exact ⟨y, htw.trans hwy, hvx.trans hxy⟩
  · rintro ⟨v, ht, hu⟩
    exact .trans _ _ _ (Relation.EqvGen.reflTransGen_le_eqvGen Parallel _ _ ht)
      (.symm _ _ (Relation.EqvGen.reflTransGen_le_eqvGen Parallel _ _ hu))

theorem root_toParallel {n : ℕ} {t u : Term n} (h : RootReduction t u) : Parallel t u := by
  cases h with
  | beta A body a => exact .beta (Parallel.rfl body) (Parallel.rfl a)
  | fst_pair a b => exact .fst_pair (Parallel.rfl _)
  | snd_pair a b => exact .snd_pair (Parallel.rfl _)
  | nat_zero C z s => exact .nat_zero (Parallel.rfl _)
  | nat_succ C z s t => exact .nat_succ (Parallel.rfl C) (Parallel.rfl z) (Parallel.rfl s) (Parallel.rfl t)
  | j_refl A a C d => exact .j_refl (Parallel.rfl _)

theorem step_toParallel {n : ℕ} {t u : Term n} (h : ReductionStep t u) : Parallel t u := by
  induction h with
  | root h => exact root_toParallel h
  | succ h ih => exact .succ ih
  | pi_domain h ih => exact .pi ih (Parallel.rfl _)
  | pi_codomain h ih => exact .pi (Parallel.rfl _) ih
  | sigma_domain h ih => exact .sigma ih (Parallel.rfl _)
  | sigma_codomain h ih => exact .sigma (Parallel.rfl _) ih
  | lam_domain h ih => exact .lam ih (Parallel.rfl _)
  | lam_body h ih => exact .lam (Parallel.rfl _) ih
  | app_function h ih => exact .app ih (Parallel.rfl _)
  | app_argument h ih => exact .app (Parallel.rfl _) ih
  | pair_left h ih => exact .pair ih (Parallel.rfl _)
  | pair_right h ih => exact .pair (Parallel.rfl _) ih
  | fst h ih => exact .fst ih
  | snd h ih => exact .snd ih
  | natrec_motive h ih => exact .natrec ih (Parallel.rfl _) (Parallel.rfl _) (Parallel.rfl _)
  | natrec_zero h ih => exact .natrec (Parallel.rfl _) ih (Parallel.rfl _) (Parallel.rfl _)
  | natrec_step h ih => exact .natrec (Parallel.rfl _) (Parallel.rfl _) ih (Parallel.rfl _)
  | natrec_scrutinee h ih => exact .natrec (Parallel.rfl _) (Parallel.rfl _) (Parallel.rfl _) ih
  | absurd_type h ih => exact .absurd ih (Parallel.rfl _)
  | absurd_term h ih => exact .absurd (Parallel.rfl _) ih
  | id_type h ih => exact .id ih (Parallel.rfl _) (Parallel.rfl _)
  | id_left h ih => exact .id (Parallel.rfl _) ih (Parallel.rfl _)
  | id_right h ih => exact .id (Parallel.rfl _) (Parallel.rfl _) ih
  | refl h ih => exact .refl ih
  | j_type h ih => exact .j ih (Parallel.rfl _) (Parallel.rfl _) (Parallel.rfl _) (Parallel.rfl _) (Parallel.rfl _)
  | j_left h ih => exact .j (Parallel.rfl _) ih (Parallel.rfl _) (Parallel.rfl _) (Parallel.rfl _) (Parallel.rfl _)
  | j_motive h ih => exact .j (Parallel.rfl _) (Parallel.rfl _) ih (Parallel.rfl _) (Parallel.rfl _) (Parallel.rfl _)
  | j_base h ih => exact .j (Parallel.rfl _) (Parallel.rfl _) (Parallel.rfl _) ih (Parallel.rfl _) (Parallel.rfl _)
  | j_right h ih => exact .j (Parallel.rfl _) (Parallel.rfl _) (Parallel.rfl _) (Parallel.rfl _) ih (Parallel.rfl _)
  | j_path h ih => exact .j (Parallel.rfl _) (Parallel.rfl _) (Parallel.rfl _) (Parallel.rfl _) (Parallel.rfl _) ih

theorem original_reduces {n : ℕ} {t u : Term n}
    (h : Silmaril.Logic.TypeTheory.IntensionalMLTT.Reduces t u) : Silmaril.Logic.TypeTheory.IntensionalMLTT.LinearJ.Reduces t u :=
  Relation.ReflTransGen.mono (fun _ _ h => step_toParallel h) _ _ h

theorem original_convertible {n : ℕ} {t u : Term n}
    (h : Silmaril.Logic.TypeTheory.IntensionalMLTT.Convertible t u) : Silmaril.Logic.TypeTheory.IntensionalMLTT.LinearJ.Convertible t u := by
  have hZ := convertible_iff_reductionZigzag.mp h
  exact Relation.EqvGen.mono (fun _ _ h => step_toParallel h) _ _ hZ


def mismatch : Term 0 := .j .unit .zero .unit .star (.succ .zero) (.refl .zero)

theorem mismatch_parallel : Parallel mismatch .star := .j_refl (.star)

private theorem unit_no_step {n : ℕ} {u : Term n} : ¬ ReductionStep (.unit : Term n) u := by
  intro h
  cases h with
  | root h => cases h

private theorem zero_no_step {n : ℕ} {u : Term n} : ¬ ReductionStep (.zero : Term n) u := by
  intro h
  cases h with
  | root h => cases h

private theorem star_no_step {n : ℕ} {u : Term n} : ¬ ReductionStep (.star : Term n) u := by
  intro h
  cases h with
  | root h => cases h

theorem mismatch_no_step {u : Term 0} : ¬ ReductionStep mismatch u := by
  intro h
  cases h with
  | root h => cases h
  | j_type h => exact unit_no_step h
  | j_left h => exact zero_no_step h
  | j_motive h => exact unit_no_step h
  | j_base h => exact star_no_step h
  | j_right h =>
    cases h with
    | root h => cases h
    | succ h => exact zero_no_step h
  | j_path h =>
    cases h with
    | root h => cases h
    | refl h => exact zero_no_step h

theorem mismatch_not_original_reduces :
    ¬ Silmaril.Logic.TypeTheory.IntensionalMLTT.Reduces mismatch .star := by
  intro h
  have heq : (.star : Term 0) = mismatch := (Relation.reflTransGen_iff_eq (fun _ => mismatch_no_step)).mp h
  cases heq

theorem strict_directed_extension : ∃ t u : Term 0,
    Silmaril.Logic.TypeTheory.IntensionalMLTT.LinearJ.Reduces t u ∧ ¬ Silmaril.Logic.TypeTheory.IntensionalMLTT.Reduces t u :=
  ⟨mismatch, .star, .single mismatch_parallel, mismatch_not_original_reduces⟩

end Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.LinearJ
