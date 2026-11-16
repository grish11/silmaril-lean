module

public import Silmaril.Logic.TypeTheory.IntensionalMLTT.Reduction.Defs

@[expose] public section

namespace Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.Reduction

open Silmaril.Logic.TypeTheory.IntensionalMLTT

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

theorem root_rename {n m : ℕ} {t u : Term n} (h : RootReduction t u) (ρ : Fin n → Fin m) :
    RootReduction (t.rename ρ) (u.rename ρ) := by
  cases h with
  | beta A body a => simpa only [Term.rename, rename_instantiate] using RootReduction.beta (A.rename ρ) (body.rename (Term.upRen ρ)) (a.rename ρ)
  | fst_pair a b => exact .fst_pair _ _
  | snd_pair a b => exact .snd_pair _ _
  | nat_zero C z s => exact .nat_zero _ _ _
  | nat_succ C z s t => exact .nat_succ _ _ _ _
  | j_refl A a C d => exact .j_refl _ _ _ _

theorem root_subst {n m : ℕ} {t u : Term n} (h : RootReduction t u) (σ : Fin n → Term m) :
    RootReduction (t.subst σ) (u.subst σ) := by
  cases h with
  | beta A body a => simpa only [Term.subst, subst_instantiate] using RootReduction.beta (A.subst σ) (body.subst (Term.upSub σ)) (a.subst σ)
  | fst_pair a b => exact .fst_pair _ _
  | snd_pair a b => exact .snd_pair _ _
  | nat_zero C z s => exact .nat_zero _ _ _
  | nat_succ C z s t => exact .nat_succ _ _ _ _
  | j_refl A a C d => exact .j_refl _ _ _ _

theorem root_convertible {n : ℕ} {t u : Term n} (h : RootReduction t u) : Convertible t u := by
  cases h with
  | beta A body a => exact ⟨.beta _ _ _⟩
  | fst_pair a b => exact ⟨.fst_pair _ _⟩
  | snd_pair a b => exact ⟨.snd_pair _ _⟩
  | nat_zero C z s => exact ⟨.nat_zero _ _ _⟩
  | nat_succ C z s t => exact ⟨.nat_succ _ _ _ _⟩
  | j_refl A a C d => exact ⟨.j_refl _ _ _ _⟩

theorem step_rename {n : ℕ} {t u : Term n} (h : ReductionStep t u)
    {m : ℕ} (ρ : Fin n → Fin m) : ReductionStep (t.rename ρ) (u.rename ρ) := by
  induction h generalizing m with
  | root h => exact .root (root_rename h ρ)
  | succ _ ih => exact .succ (ih ρ)
  | pi_domain _ ih => exact .pi_domain (ih ρ)
  | pi_codomain _ ih => exact .pi_codomain (ih (Term.upRen ρ))
  | sigma_domain _ ih => exact .sigma_domain (ih ρ)
  | sigma_codomain _ ih => exact .sigma_codomain (ih (Term.upRen ρ))
  | lam_domain _ ih => exact .lam_domain (ih ρ)
  | lam_body _ ih => exact .lam_body (ih (Term.upRen ρ))
  | app_function _ ih => exact .app_function (ih ρ)
  | app_argument _ ih => exact .app_argument (ih ρ)
  | pair_left _ ih => exact .pair_left (ih ρ)
  | pair_right _ ih => exact .pair_right (ih ρ)
  | fst _ ih => exact .fst (ih ρ)
  | snd _ ih => exact .snd (ih ρ)
  | natrec_motive _ ih => exact .natrec_motive (ih (Term.upRen ρ))
  | natrec_zero _ ih => exact .natrec_zero (ih ρ)
  | natrec_step _ ih => exact .natrec_step (ih ρ)
  | natrec_scrutinee _ ih => exact .natrec_scrutinee (ih ρ)
  | absurd_type _ ih => exact .absurd_type (ih ρ)
  | absurd_term _ ih => exact .absurd_term (ih ρ)
  | id_type _ ih => exact .id_type (ih ρ)
  | id_left _ ih => exact .id_left (ih ρ)
  | id_right _ ih => exact .id_right (ih ρ)
  | refl _ ih => exact .refl (ih ρ)
  | j_type _ ih => exact .j_type (ih ρ)
  | j_left _ ih => exact .j_left (ih ρ)
  | j_motive _ ih => exact .j_motive (ih (Term.upRen (Term.upRen ρ)))
  | j_base _ ih => exact .j_base (ih ρ)
  | j_right _ ih => exact .j_right (ih ρ)
  | j_path _ ih => exact .j_path (ih ρ)

theorem step_subst {n : ℕ} {t u : Term n} (h : ReductionStep t u)
    {m : ℕ} (σ : Fin n → Term m) : ReductionStep (t.subst σ) (u.subst σ) := by
  induction h generalizing m with
  | root h => exact .root (root_subst h σ)
  | succ _ ih => exact .succ (ih σ)
  | pi_domain _ ih => exact .pi_domain (ih σ)
  | pi_codomain _ ih => exact .pi_codomain (ih (Term.upSub σ))
  | sigma_domain _ ih => exact .sigma_domain (ih σ)
  | sigma_codomain _ ih => exact .sigma_codomain (ih (Term.upSub σ))
  | lam_domain _ ih => exact .lam_domain (ih σ)
  | lam_body _ ih => exact .lam_body (ih (Term.upSub σ))
  | app_function _ ih => exact .app_function (ih σ)
  | app_argument _ ih => exact .app_argument (ih σ)
  | pair_left _ ih => exact .pair_left (ih σ)
  | pair_right _ ih => exact .pair_right (ih σ)
  | fst _ ih => exact .fst (ih σ)
  | snd _ ih => exact .snd (ih σ)
  | natrec_motive _ ih => exact .natrec_motive (ih (Term.upSub σ))
  | natrec_zero _ ih => exact .natrec_zero (ih σ)
  | natrec_step _ ih => exact .natrec_step (ih σ)
  | natrec_scrutinee _ ih => exact .natrec_scrutinee (ih σ)
  | absurd_type _ ih => exact .absurd_type (ih σ)
  | absurd_term _ ih => exact .absurd_term (ih σ)
  | id_type _ ih => exact .id_type (ih σ)
  | id_left _ ih => exact .id_left (ih σ)
  | id_right _ ih => exact .id_right (ih σ)
  | refl _ ih => exact .refl (ih σ)
  | j_type _ ih => exact .j_type (ih σ)
  | j_left _ ih => exact .j_left (ih σ)
  | j_motive _ ih => exact .j_motive (ih (Term.upSub (Term.upSub σ)))
  | j_base _ ih => exact .j_base (ih σ)
  | j_right _ ih => exact .j_right (ih σ)
  | j_path _ ih => exact .j_path (ih σ)

theorem step_convertible {n : ℕ} {t u : Term n} (h : ReductionStep t u) : Convertible t u := by
  induction h with
  | root h => exact root_convertible h
  | succ _ ih => obtain ⟨ih⟩ := ih; exact ⟨.congr_succ ih⟩
  | pi_domain _ ih => obtain ⟨ih⟩ := ih; exact ⟨.congr_pi ih (.refl _)⟩
  | pi_codomain _ ih => obtain ⟨ih⟩ := ih; exact ⟨.congr_pi (.refl _) ih⟩
  | sigma_domain _ ih => obtain ⟨ih⟩ := ih; exact ⟨.congr_sigma ih (.refl _)⟩
  | sigma_codomain _ ih => obtain ⟨ih⟩ := ih; exact ⟨.congr_sigma (.refl _) ih⟩
  | lam_domain _ ih => obtain ⟨ih⟩ := ih; exact ⟨.congr_lam ih (.refl _)⟩
  | lam_body _ ih => obtain ⟨ih⟩ := ih; exact ⟨.congr_lam (.refl _) ih⟩
  | app_function _ ih => obtain ⟨ih⟩ := ih; exact ⟨.congr_app ih (.refl _)⟩
  | app_argument _ ih => obtain ⟨ih⟩ := ih; exact ⟨.congr_app (.refl _) ih⟩
  | pair_left _ ih => obtain ⟨ih⟩ := ih; exact ⟨.congr_pair ih (.refl _)⟩
  | pair_right _ ih => obtain ⟨ih⟩ := ih; exact ⟨.congr_pair (.refl _) ih⟩
  | fst _ ih => obtain ⟨ih⟩ := ih; exact ⟨.congr_fst ih⟩
  | snd _ ih => obtain ⟨ih⟩ := ih; exact ⟨.congr_snd ih⟩
  | natrec_motive _ ih => obtain ⟨ih⟩ := ih; exact ⟨.congr_natrec ih (.refl _) (.refl _) (.refl _)⟩
  | natrec_zero _ ih => obtain ⟨ih⟩ := ih; exact ⟨.congr_natrec (.refl _) ih (.refl _) (.refl _)⟩
  | natrec_step _ ih => obtain ⟨ih⟩ := ih; exact ⟨.congr_natrec (.refl _) (.refl _) ih (.refl _)⟩
  | natrec_scrutinee _ ih => obtain ⟨ih⟩ := ih; exact ⟨.congr_natrec (.refl _) (.refl _) (.refl _) ih⟩
  | absurd_type _ ih => obtain ⟨ih⟩ := ih; exact ⟨.congr_absurd ih (.refl _)⟩
  | absurd_term _ ih => obtain ⟨ih⟩ := ih; exact ⟨.congr_absurd (.refl _) ih⟩
  | id_type _ ih => obtain ⟨ih⟩ := ih; exact ⟨.congr_id ih (.refl _) (.refl _)⟩
  | id_left _ ih => obtain ⟨ih⟩ := ih; exact ⟨.congr_id (.refl _) ih (.refl _)⟩
  | id_right _ ih => obtain ⟨ih⟩ := ih; exact ⟨.congr_id (.refl _) (.refl _) ih⟩
  | refl _ ih => obtain ⟨ih⟩ := ih; exact ⟨.congr_refl ih⟩
  | j_type _ ih => obtain ⟨ih⟩ := ih; exact ⟨.congr_j ih (.refl _) (.refl _) (.refl _) (.refl _) (.refl _)⟩
  | j_left _ ih => obtain ⟨ih⟩ := ih; exact ⟨.congr_j (.refl _) ih (.refl _) (.refl _) (.refl _) (.refl _)⟩
  | j_motive _ ih => obtain ⟨ih⟩ := ih; exact ⟨.congr_j (.refl _) (.refl _) ih (.refl _) (.refl _) (.refl _)⟩
  | j_base _ ih => obtain ⟨ih⟩ := ih; exact ⟨.congr_j (.refl _) (.refl _) (.refl _) ih (.refl _) (.refl _)⟩
  | j_right _ ih => obtain ⟨ih⟩ := ih; exact ⟨.congr_j (.refl _) (.refl _) (.refl _) (.refl _) ih (.refl _)⟩
  | j_path _ ih => obtain ⟨ih⟩ := ih; exact ⟨.congr_j (.refl _) (.refl _) (.refl _) (.refl _) (.refl _) ih⟩

theorem reduces_map {n m : ℕ} (f : Term n → Term m)
    (hf : ∀ {t u}, ReductionStep t u → ReductionStep (f t) (f u))
    {t u : Term n} (h : Reduces t u) : Reduces (f t) (f u) :=
  Relation.ReflTransGen.lift f (fun _ _ h => hf h) t u h

theorem zigzag_map {n m : ℕ} (f : Term n → Term m)
    (hf : ∀ {t u}, ReductionStep t u → ReductionStep (f t) (f u))
    {t u : Term n} (h : ReductionZigzag t u) : ReductionZigzag (f t) (f u) := by
  induction h with
  | rel t u h => exact .rel _ _ (hf h)
  | refl t => exact .refl _
  | symm t u _ ih => exact .symm _ _ ih
  | trans t u v _ _ ih ik => exact .trans _ _ _ ih ik

theorem reduces_congr_succ {n : ℕ} {t t' : Term n}
    (ht : Reduces t t') :
    Reduces (.succ t) (.succ t') := by
  have h0 := reduces_map (fun v => (.succ v)) (fun h => ReductionStep.succ h) ht
  exact h0

theorem reduces_congr_pi {n : ℕ} {A A' : Term n} {B B' : Term (n + 1)}
    (hA : Reduces A A') (hB : Reduces B B') :
    Reduces (.pi A B) (.pi A' B') := by
  have h0 := reduces_map (fun v => (.pi v B)) (fun h => ReductionStep.pi_domain h) hA
  have h1 := reduces_map (fun v => (.pi A' v)) (fun h => ReductionStep.pi_codomain h) hB
  exact (h0).trans h1

theorem reduces_congr_sigma {n : ℕ} {A A' : Term n} {B B' : Term (n + 1)}
    (hA : Reduces A A') (hB : Reduces B B') :
    Reduces (.sigma A B) (.sigma A' B') := by
  have h0 := reduces_map (fun v => (.sigma v B)) (fun h => ReductionStep.sigma_domain h) hA
  have h1 := reduces_map (fun v => (.sigma A' v)) (fun h => ReductionStep.sigma_codomain h) hB
  exact (h0).trans h1

theorem reduces_congr_lam {n : ℕ} {A A' : Term n} {body body' : Term (n + 1)}
    (hA : Reduces A A') (hbody : Reduces body body') :
    Reduces (.lam A body) (.lam A' body') := by
  have h0 := reduces_map (fun v => (.lam v body)) (fun h => ReductionStep.lam_domain h) hA
  have h1 := reduces_map (fun v => (.lam A' v)) (fun h => ReductionStep.lam_body h) hbody
  exact (h0).trans h1

theorem reduces_congr_app {n : ℕ} {f f' : Term n} {a a' : Term n}
    (hf : Reduces f f') (ha : Reduces a a') :
    Reduces (.app f a) (.app f' a') := by
  have h0 := reduces_map (fun v => (.app v a)) (fun h => ReductionStep.app_function h) hf
  have h1 := reduces_map (fun v => (.app f' v)) (fun h => ReductionStep.app_argument h) ha
  exact (h0).trans h1

theorem reduces_congr_pair {n : ℕ} {a a' : Term n} {b b' : Term n}
    (ha : Reduces a a') (hb : Reduces b b') :
    Reduces (.pair a b) (.pair a' b') := by
  have h0 := reduces_map (fun v => (.pair v b)) (fun h => ReductionStep.pair_left h) ha
  have h1 := reduces_map (fun v => (.pair a' v)) (fun h => ReductionStep.pair_right h) hb
  exact (h0).trans h1

theorem reduces_congr_fst {n : ℕ} {p p' : Term n}
    (hp : Reduces p p') :
    Reduces (.fst p) (.fst p') := by
  have h0 := reduces_map (fun v => (.fst v)) (fun h => ReductionStep.fst h) hp
  exact h0

theorem reduces_congr_snd {n : ℕ} {p p' : Term n}
    (hp : Reduces p p') :
    Reduces (.snd p) (.snd p') := by
  have h0 := reduces_map (fun v => (.snd v)) (fun h => ReductionStep.snd h) hp
  exact h0

theorem reduces_congr_natrec {n : ℕ} {C C' : Term (n + 1)} {z z' : Term n} {s s' : Term n} {t t' : Term n}
    (hC : Reduces C C') (hz : Reduces z z') (hs : Reduces s s') (ht : Reduces t t') :
    Reduces (.natrec C z s t) (.natrec C' z' s' t') := by
  have h0 := reduces_map (fun v => (.natrec v z s t)) (fun h => ReductionStep.natrec_motive h) hC
  have h1 := reduces_map (fun v => (.natrec C' v s t)) (fun h => ReductionStep.natrec_zero h) hz
  have h2 := reduces_map (fun v => (.natrec C' z' v t)) (fun h => ReductionStep.natrec_step h) hs
  have h3 := reduces_map (fun v => (.natrec C' z' s' v)) (fun h => ReductionStep.natrec_scrutinee h) ht
  exact (((h0).trans h1).trans h2).trans h3

theorem reduces_congr_absurd {n : ℕ} {A A' : Term n} {e e' : Term n}
    (hA : Reduces A A') (he : Reduces e e') :
    Reduces (.absurd A e) (.absurd A' e') := by
  have h0 := reduces_map (fun v => (.absurd v e)) (fun h => ReductionStep.absurd_type h) hA
  have h1 := reduces_map (fun v => (.absurd A' v)) (fun h => ReductionStep.absurd_term h) he
  exact (h0).trans h1

theorem reduces_congr_id {n : ℕ} {A A' : Term n} {a a' : Term n} {b b' : Term n}
    (hA : Reduces A A') (ha : Reduces a a') (hb : Reduces b b') :
    Reduces (.id A a b) (.id A' a' b') := by
  have h0 := reduces_map (fun v => (.id v a b)) (fun h => ReductionStep.id_type h) hA
  have h1 := reduces_map (fun v => (.id A' v b)) (fun h => ReductionStep.id_left h) ha
  have h2 := reduces_map (fun v => (.id A' a' v)) (fun h => ReductionStep.id_right h) hb
  exact ((h0).trans h1).trans h2

theorem reduces_congr_refl {n : ℕ} {a a' : Term n}
    (ha : Reduces a a') :
    Reduces (.refl a) (.refl a') := by
  have h0 := reduces_map (fun v => (.refl v)) (fun h => ReductionStep.refl h) ha
  exact h0

theorem reduces_congr_j {n : ℕ} {A A' : Term n} {a a' : Term n} {C C' : Term (n + 2)} {d d' : Term n} {b b' : Term n} {p p' : Term n}
    (hA : Reduces A A') (ha : Reduces a a') (hC : Reduces C C') (hd : Reduces d d') (hb : Reduces b b') (hp : Reduces p p') :
    Reduces (.j A a C d b p) (.j A' a' C' d' b' p') := by
  have h0 := reduces_map (fun v => (.j v a C d b p)) (fun h => ReductionStep.j_type h) hA
  have h1 := reduces_map (fun v => (.j A' v C d b p)) (fun h => ReductionStep.j_left h) ha
  have h2 := reduces_map (fun v => (.j A' a' v d b p)) (fun h => ReductionStep.j_motive h) hC
  have h3 := reduces_map (fun v => (.j A' a' C' v b p)) (fun h => ReductionStep.j_base h) hd
  have h4 := reduces_map (fun v => (.j A' a' C' d' v p)) (fun h => ReductionStep.j_right h) hb
  have h5 := reduces_map (fun v => (.j A' a' C' d' b' v)) (fun h => ReductionStep.j_path h) hp
  exact (((((h0).trans h1).trans h2).trans h3).trans h4).trans h5

theorem zigzag_congr_succ {n : ℕ} {t t' : Term n}
    (ht : ReductionZigzag t t') :
    ReductionZigzag (.succ t) (.succ t') := by
  have h0 := zigzag_map (fun v => (.succ v)) (fun h => ReductionStep.succ h) ht
  exact h0

theorem zigzag_congr_pi {n : ℕ} {A A' : Term n} {B B' : Term (n + 1)}
    (hA : ReductionZigzag A A') (hB : ReductionZigzag B B') :
    ReductionZigzag (.pi A B) (.pi A' B') := by
  have h0 := zigzag_map (fun v => (.pi v B)) (fun h => ReductionStep.pi_domain h) hA
  have h1 := zigzag_map (fun v => (.pi A' v)) (fun h => ReductionStep.pi_codomain h) hB
  exact Relation.EqvGen.trans _ _ _ (h0) h1

theorem zigzag_congr_sigma {n : ℕ} {A A' : Term n} {B B' : Term (n + 1)}
    (hA : ReductionZigzag A A') (hB : ReductionZigzag B B') :
    ReductionZigzag (.sigma A B) (.sigma A' B') := by
  have h0 := zigzag_map (fun v => (.sigma v B)) (fun h => ReductionStep.sigma_domain h) hA
  have h1 := zigzag_map (fun v => (.sigma A' v)) (fun h => ReductionStep.sigma_codomain h) hB
  exact Relation.EqvGen.trans _ _ _ (h0) h1

theorem zigzag_congr_lam {n : ℕ} {A A' : Term n} {body body' : Term (n + 1)}
    (hA : ReductionZigzag A A') (hbody : ReductionZigzag body body') :
    ReductionZigzag (.lam A body) (.lam A' body') := by
  have h0 := zigzag_map (fun v => (.lam v body)) (fun h => ReductionStep.lam_domain h) hA
  have h1 := zigzag_map (fun v => (.lam A' v)) (fun h => ReductionStep.lam_body h) hbody
  exact Relation.EqvGen.trans _ _ _ (h0) h1

theorem zigzag_congr_app {n : ℕ} {f f' : Term n} {a a' : Term n}
    (hf : ReductionZigzag f f') (ha : ReductionZigzag a a') :
    ReductionZigzag (.app f a) (.app f' a') := by
  have h0 := zigzag_map (fun v => (.app v a)) (fun h => ReductionStep.app_function h) hf
  have h1 := zigzag_map (fun v => (.app f' v)) (fun h => ReductionStep.app_argument h) ha
  exact Relation.EqvGen.trans _ _ _ (h0) h1

theorem zigzag_congr_pair {n : ℕ} {a a' : Term n} {b b' : Term n}
    (ha : ReductionZigzag a a') (hb : ReductionZigzag b b') :
    ReductionZigzag (.pair a b) (.pair a' b') := by
  have h0 := zigzag_map (fun v => (.pair v b)) (fun h => ReductionStep.pair_left h) ha
  have h1 := zigzag_map (fun v => (.pair a' v)) (fun h => ReductionStep.pair_right h) hb
  exact Relation.EqvGen.trans _ _ _ (h0) h1

theorem zigzag_congr_fst {n : ℕ} {p p' : Term n}
    (hp : ReductionZigzag p p') :
    ReductionZigzag (.fst p) (.fst p') := by
  have h0 := zigzag_map (fun v => (.fst v)) (fun h => ReductionStep.fst h) hp
  exact h0

theorem zigzag_congr_snd {n : ℕ} {p p' : Term n}
    (hp : ReductionZigzag p p') :
    ReductionZigzag (.snd p) (.snd p') := by
  have h0 := zigzag_map (fun v => (.snd v)) (fun h => ReductionStep.snd h) hp
  exact h0

theorem zigzag_congr_natrec {n : ℕ} {C C' : Term (n + 1)} {z z' : Term n} {s s' : Term n} {t t' : Term n}
    (hC : ReductionZigzag C C') (hz : ReductionZigzag z z') (hs : ReductionZigzag s s') (ht : ReductionZigzag t t') :
    ReductionZigzag (.natrec C z s t) (.natrec C' z' s' t') := by
  have h0 := zigzag_map (fun v => (.natrec v z s t)) (fun h => ReductionStep.natrec_motive h) hC
  have h1 := zigzag_map (fun v => (.natrec C' v s t)) (fun h => ReductionStep.natrec_zero h) hz
  have h2 := zigzag_map (fun v => (.natrec C' z' v t)) (fun h => ReductionStep.natrec_step h) hs
  have h3 := zigzag_map (fun v => (.natrec C' z' s' v)) (fun h => ReductionStep.natrec_scrutinee h) ht
  exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.trans _ _ _ (Relation.EqvGen.trans _ _ _ (h0) h1) h2) h3

theorem zigzag_congr_absurd {n : ℕ} {A A' : Term n} {e e' : Term n}
    (hA : ReductionZigzag A A') (he : ReductionZigzag e e') :
    ReductionZigzag (.absurd A e) (.absurd A' e') := by
  have h0 := zigzag_map (fun v => (.absurd v e)) (fun h => ReductionStep.absurd_type h) hA
  have h1 := zigzag_map (fun v => (.absurd A' v)) (fun h => ReductionStep.absurd_term h) he
  exact Relation.EqvGen.trans _ _ _ (h0) h1

theorem zigzag_congr_id {n : ℕ} {A A' : Term n} {a a' : Term n} {b b' : Term n}
    (hA : ReductionZigzag A A') (ha : ReductionZigzag a a') (hb : ReductionZigzag b b') :
    ReductionZigzag (.id A a b) (.id A' a' b') := by
  have h0 := zigzag_map (fun v => (.id v a b)) (fun h => ReductionStep.id_type h) hA
  have h1 := zigzag_map (fun v => (.id A' v b)) (fun h => ReductionStep.id_left h) ha
  have h2 := zigzag_map (fun v => (.id A' a' v)) (fun h => ReductionStep.id_right h) hb
  exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.trans _ _ _ (h0) h1) h2

theorem zigzag_congr_refl {n : ℕ} {a a' : Term n}
    (ha : ReductionZigzag a a') :
    ReductionZigzag (.refl a) (.refl a') := by
  have h0 := zigzag_map (fun v => (.refl v)) (fun h => ReductionStep.refl h) ha
  exact h0

theorem zigzag_congr_j {n : ℕ} {A A' : Term n} {a a' : Term n} {C C' : Term (n + 2)} {d d' : Term n} {b b' : Term n} {p p' : Term n}
    (hA : ReductionZigzag A A') (ha : ReductionZigzag a a') (hC : ReductionZigzag C C') (hd : ReductionZigzag d d') (hb : ReductionZigzag b b') (hp : ReductionZigzag p p') :
    ReductionZigzag (.j A a C d b p) (.j A' a' C' d' b' p') := by
  have h0 := zigzag_map (fun v => (.j v a C d b p)) (fun h => ReductionStep.j_type h) hA
  have h1 := zigzag_map (fun v => (.j A' v C d b p)) (fun h => ReductionStep.j_left h) ha
  have h2 := zigzag_map (fun v => (.j A' a' v d b p)) (fun h => ReductionStep.j_motive h) hC
  have h3 := zigzag_map (fun v => (.j A' a' C' v b p)) (fun h => ReductionStep.j_base h) hd
  have h4 := zigzag_map (fun v => (.j A' a' C' d' v p)) (fun h => ReductionStep.j_right h) hb
  have h5 := zigzag_map (fun v => (.j A' a' C' d' b' v)) (fun h => ReductionStep.j_path h) hp
  exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.trans _ _ _ (Relation.EqvGen.trans _ _ _ (Relation.EqvGen.trans _ _ _ (Relation.EqvGen.trans _ _ _ (h0) h1) h2) h3) h4) h5

theorem conversion_zigzag {n : ℕ} {t u : Term n} (h : Conversion t u) : ReductionZigzag t u := by
  induction h with
  | refl t => exact .refl t
  | symm _ ih => exact .symm _ _ ih
  | trans _ _ ih ik => exact .trans _ _ _ ih ik
  | beta A body a => exact .rel _ _ (.root (.beta A body a))
  | fst_pair a b => exact .rel _ _ (.root (.fst_pair a b))
  | snd_pair a b => exact .rel _ _ (.root (.snd_pair a b))
  | nat_zero C z s => exact .rel _ _ (.root (.nat_zero C z s))
  | nat_succ C z s t => exact .rel _ _ (.root (.nat_succ C z s t))
  | j_refl A a C d => exact .rel _ _ (.root (.j_refl A a C d))
  | congr_succ _ ht => exact zigzag_congr_succ ht
  | congr_pi _ _ hA hB => exact zigzag_congr_pi hA hB
  | congr_sigma _ _ hA hB => exact zigzag_congr_sigma hA hB
  | congr_lam _ _ hA hbody => exact zigzag_congr_lam hA hbody
  | congr_app _ _ hf ha => exact zigzag_congr_app hf ha
  | congr_pair _ _ ha hb => exact zigzag_congr_pair ha hb
  | congr_fst _ hp => exact zigzag_congr_fst hp
  | congr_snd _ hp => exact zigzag_congr_snd hp
  | congr_natrec _ _ _ _ hC hz hs ht => exact zigzag_congr_natrec hC hz hs ht
  | congr_absurd _ _ hA he => exact zigzag_congr_absurd hA he
  | congr_id _ _ _ hA ha hb => exact zigzag_congr_id hA ha hb
  | congr_refl _ ha => exact zigzag_congr_refl ha
  | congr_j _ _ _ _ _ _ hA ha hC hd hb hp => exact zigzag_congr_j hA ha hC hd hb hp

theorem zigzag_convertible {n : ℕ} {t u : Term n} (h : ReductionZigzag t u) : Convertible t u := by
  induction h with
  | rel t u h => exact step_convertible h
  | refl t => exact ⟨.refl t⟩
  | symm t u _ ih => obtain ⟨ih⟩ := ih; exact ⟨.symm ih⟩
  | trans t u v _ _ ih ik => obtain ⟨ih⟩ := ih; obtain ⟨ik⟩ := ik; exact ⟨.trans ih ik⟩

end Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.Reduction
