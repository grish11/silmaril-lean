module

public import Silmaril.Logic.TypeTheory.IntensionalMLTT.Substitution.Defs

public section

namespace Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.Substitution

open Silmaril.Logic.TypeTheory.IntensionalMLTT

theorem rename_weaken {n m : ℕ} (t : Term n) (ρ : Fin n → Fin m) :
    t.weaken.rename (Term.upRen ρ) = (t.rename ρ).weaken := by
  simp only [Term.weaken, Term.rename_comp]
  rfl

theorem subst_weaken {n m : ℕ} (t : Term n) (σ : Fin n → Term m) :
    t.weaken.subst (Term.upSub σ) = (t.subst σ).weaken := by
  rw [Term.weaken, Term.subst_rename, Term.weaken, Term.rename_subst]
  rfl

theorem rename_instantiate {n m : ℕ} (t : Term (n + 1)) (a : Term n)
    (ρ : Fin n → Fin m) :
    (t.instantiate a).rename ρ = (t.rename (Term.upRen ρ)).instantiate (a.rename ρ) := by
  simp only [Term.instantiate, Term.rename_subst, Term.subst_rename]
  congr 1
  funext i
  cases i using Fin.cases <;> rfl

theorem subst_instantiate {n m : ℕ} (t : Term (n + 1)) (a : Term n)
    (σ : Fin n → Term m) :
    (t.instantiate a).subst σ = (t.subst (Term.upSub σ)).instantiate (a.subst σ) := by
  simp only [Term.instantiate, Term.subst_comp]
  congr 1
  funext i
  cases i using Fin.cases with
  | zero => rfl
  | succ i => exact (Term.instantiate_weaken (σ i) (a.subst σ)).symm

theorem rename_instantiate₂ {n m : ℕ} (t : Term (n + 2)) (a p : Term n)
    (ρ : Fin n → Fin m) :
    (t.instantiate₂ a p).rename ρ =
      (t.rename (Term.upRen (Term.upRen ρ))).instantiate₂ (a.rename ρ) (p.rename ρ) := by
  simp only [Term.instantiate₂, Term.rename_subst, Term.subst_rename]
  congr 1
  funext i
  cases i using Fin.cases with
  | zero => rfl
  | succ i => cases i using Fin.cases <;> rfl

theorem subst_instantiate₂ {n m : ℕ} (t : Term (n + 2)) (a p : Term n)
    (σ : Fin n → Term m) :
    (t.instantiate₂ a p).subst σ =
      (t.subst (Term.upSub (Term.upSub σ))).instantiate₂ (a.subst σ) (p.subst σ) := by
  simp only [Term.instantiate₂, Term.subst_comp]
  congr 1
  funext i
  cases i using Fin.cases with
  | zero => rfl
  | succ i =>
    cases i using Fin.cases with
    | zero => rfl
    | succ i =>
      change σ i = (((σ i).rename Fin.succ).rename Fin.succ).subst _
      rw [Term.subst_rename, Term.subst_rename]
      exact (Term.subst_var (σ i)).symm

noncomputable def conversion_rename {n : ℕ} {t u : Term n} (h : Conversion t u)
    {m : ℕ} (ρ : Fin n → Fin m) : Conversion (t.rename ρ) (u.rename ρ) := by
  induction h generalizing m with
  | refl t => exact .refl _
  | symm _ ih => exact .symm (ih ρ)
  | trans _ _ ih ik => exact .trans (ih ρ) (ik ρ)
  | beta A body a =>
    simpa only [Term.rename, rename_instantiate] using
      Conversion.beta (A.rename ρ) (body.rename (Term.upRen ρ)) (a.rename ρ)
  | fst_pair a b => exact .fst_pair _ _
  | snd_pair a b => exact .snd_pair _ _
  | nat_zero C z s => exact .nat_zero _ _ _
  | nat_succ C z s t => exact .nat_succ _ _ _ _
  | j_refl A a C d => exact .j_refl _ _ _ _
  | congr_succ _ ih => exact .congr_succ (ih ρ)
  | congr_pi _ _ ih ik => exact .congr_pi (ih ρ) (ik (Term.upRen ρ))
  | congr_sigma _ _ ih ik => exact .congr_sigma (ih ρ) (ik (Term.upRen ρ))
  | congr_lam _ _ ih ik => exact .congr_lam (ih ρ) (ik (Term.upRen ρ))
  | congr_app _ _ ih ik => exact .congr_app (ih ρ) (ik ρ)
  | congr_pair _ _ ih ik => exact .congr_pair (ih ρ) (ik ρ)
  | congr_fst _ ih => exact .congr_fst (ih ρ)
  | congr_snd _ ih => exact .congr_snd (ih ρ)
  | congr_natrec _ _ _ _ ih iz is it => exact .congr_natrec (ih (Term.upRen ρ)) (iz ρ) (is ρ) (it ρ)
  | congr_absurd _ _ ih ik => exact .congr_absurd (ih ρ) (ik ρ)
  | congr_id _ _ _ ih ia ib => exact .congr_id (ih ρ) (ia ρ) (ib ρ)
  | congr_refl _ ih => exact .congr_refl (ih ρ)
  | congr_j _ _ _ _ _ _ ih ia ic id ib ip =>
    exact .congr_j (ih ρ) (ia ρ) (ic (Term.upRen (Term.upRen ρ))) (id ρ) (ib ρ) (ip ρ)

noncomputable def conversion_subst {n : ℕ} {t u : Term n} (h : Conversion t u)
    {m : ℕ} (σ : Fin n → Term m) : Conversion (t.subst σ) (u.subst σ) := by
  induction h generalizing m with
  | refl t => exact .refl _
  | symm _ ih => exact .symm (ih σ)
  | trans _ _ ih ik => exact .trans (ih σ) (ik σ)
  | beta A body a =>
    simpa only [Term.subst, subst_instantiate] using
      Conversion.beta (A.subst σ) (body.subst (Term.upSub σ)) (a.subst σ)
  | fst_pair a b => exact .fst_pair _ _
  | snd_pair a b => exact .snd_pair _ _
  | nat_zero C z s => exact .nat_zero _ _ _
  | nat_succ C z s t => exact .nat_succ _ _ _ _
  | j_refl A a C d => exact .j_refl _ _ _ _
  | congr_succ _ ih => exact .congr_succ (ih σ)
  | congr_pi _ _ ih ik => exact .congr_pi (ih σ) (ik (Term.upSub σ))
  | congr_sigma _ _ ih ik => exact .congr_sigma (ih σ) (ik (Term.upSub σ))
  | congr_lam _ _ ih ik => exact .congr_lam (ih σ) (ik (Term.upSub σ))
  | congr_app _ _ ih ik => exact .congr_app (ih σ) (ik σ)
  | congr_pair _ _ ih ik => exact .congr_pair (ih σ) (ik σ)
  | congr_fst _ ih => exact .congr_fst (ih σ)
  | congr_snd _ ih => exact .congr_snd (ih σ)
  | congr_natrec _ _ _ _ ih iz is it => exact .congr_natrec (ih (Term.upSub σ)) (iz σ) (is σ) (it σ)
  | congr_absurd _ _ ih ik => exact .congr_absurd (ih σ) (ik σ)
  | congr_id _ _ _ ih ia ib => exact .congr_id (ih σ) (ia σ) (ib σ)
  | congr_refl _ ih => exact .congr_refl (ih σ)
  | congr_j _ _ _ _ _ _ ih ia ic id ib ip =>
    exact .congr_j (ih σ) (ia σ) (ic (Term.upSub (Term.upSub σ))) (id σ) (ib σ) (ip σ)

theorem renaming_lift {n m : ℕ} {Γ : Context n} {Δ : Context m} {ρ : Fin n → Fin m}
    (hρ : Renaming Γ Δ ρ) (A : Term n) :
    Renaming (Γ.snoc A) (Δ.snoc (A.rename ρ)) (Term.upRen ρ) := by
  intro i B hi
  cases hi with
  | here =>
    change Lookup _ 0 (A.weaken.rename (Term.upRen ρ))
    rw [rename_weaken]
    exact .here
  | there hi =>
    rw [rename_weaken]
    exact .there (hρ hi)

theorem renaming_weaken {n : ℕ} (Γ : Context n) (A : Term n) :
    Renaming Γ (Γ.snoc A) Fin.succ := by
  intro i B hi
  exact .there hi

theorem renaming_comp {n m k : ℕ} {Γ : Context n} {Δ : Context m} {Θ : Context k}
    {ρ : Fin n → Fin m} {τ : Fin m → Fin k}
    (hρ : Renaming Γ Δ ρ) (hτ : Renaming Δ Θ τ) : Renaming Γ Θ (τ ∘ ρ) := by
  intro i A hi
  rw [← Term.rename_comp]
  exact hτ (hρ hi)

theorem rename_natStepType {n m : ℕ} (C : Term (n + 1)) (ρ : Fin n → Fin m) :
    C.natStepType.rename ρ = (C.rename (Term.upRen ρ)).natStepType := by
  simp only [Term.natStepType, Term.rename, Term.rename_subst, Term.subst_rename]
  congr 3
  funext i
  cases i using Fin.cases <;> rfl

noncomputable def derivation_rename {n : ℕ} {Γ : Context n} {t A : Term n}
    (h : Derivation Γ t A) {m : ℕ} {Δ : Context m} (hΔ : ContextDerivation Δ)
    (ρ : Fin n → Fin m) (hρ : Renaming Γ Δ ρ) :
    Derivation Δ (t.rename ρ) (A.rename ρ) := by
  induction h using Derivation.rec (motive_1 := fun _ _ => PUnit) generalizing m with
  | nil => exact ⟨⟩
  | snoc _ _ _ _ => exact ⟨⟩
  | univ _ i _ => exact .univ hΔ i
  | nat _ _ => exact .nat hΔ
  | empty _ _ => exact .empty hΔ
  | unit _ _ => exact .unit hΔ
  | var _ hi _ => exact .var hΔ (hρ hi)
  | pi hA hB ihA ihB =>
    exact .pi (ihA hΔ ρ hρ)
      (ihB (.snoc hΔ (ihA hΔ ρ hρ)) _ (renaming_lift hρ _))
  | sigma hA hB ihA ihB =>
    exact .sigma (ihA hΔ ρ hρ)
      (ihB (.snoc hΔ (ihA hΔ ρ hρ)) _ (renaming_lift hρ _))
  | lam hA hB ht ihA ihB iht =>
    exact .lam (ihA hΔ ρ hρ)
      (ihB (.snoc hΔ (ihA hΔ ρ hρ)) _ (renaming_lift hρ _))
      (iht (.snoc hΔ (ihA hΔ ρ hρ)) _ (renaming_lift hρ _))
  | app hf ha ihf iha =>
    simpa only [Term.rename, rename_instantiate] using
      Derivation.app (ihf hΔ ρ hρ) (iha hΔ ρ hρ)
  | pair hA hB ha hb ihA ihB iha ihb =>
    apply Derivation.pair (ihA hΔ ρ hρ)
      (ihB (.snoc hΔ (ihA hΔ ρ hρ)) _ (renaming_lift hρ _))
      (iha hΔ ρ hρ)
    simpa only [rename_instantiate] using ihb hΔ ρ hρ
  | fst hp ihp => exact .fst (ihp hΔ ρ hρ)
  | snd hp ihp =>
    simpa only [Term.rename, rename_instantiate] using Derivation.snd (ihp hΔ ρ hρ)
  | zero _ _ => exact .zero hΔ
  | succ ht iht => exact .succ (iht hΔ ρ hρ)
  | natrec hC hz hs ht ihC ihz ihs iht =>
    have hNat := Derivation.nat hΔ
    simpa only [Term.rename, rename_instantiate] using
      Derivation.natrec
        (ihC (.snoc hΔ hNat) _ (renaming_lift hρ _))
        (by simpa only [Term.rename, rename_instantiate] using ihz hΔ ρ hρ)
        (by simpa only [rename_natStepType] using ihs hΔ ρ hρ)
        (iht hΔ ρ hρ)
  | star _ _ => exact .star hΔ
  | absurd hA he ihA ihe => exact .absurd (ihA hΔ ρ hρ) (ihe hΔ ρ hρ)
  | id hA ha hb ihA iha ihb => exact .id (ihA hΔ ρ hρ) (iha hΔ ρ hρ) (ihb hΔ ρ hρ)
  | refl hA ha ihA iha => exact .refl (ihA hΔ ρ hρ) (iha hΔ ρ hρ)
  | j hA ha hC hd hb hp ihA iha ihC ihd ihb ihp =>
    rename_i n i j Γ A a d b p C
    have hA' := ihA hΔ ρ hρ
    have ha' := iha hΔ ρ hρ
    have hExt := ContextDerivation.snoc hΔ hA'
    have hρ' : Renaming (Γ.snoc A) _ (Term.upRen ρ) := renaming_lift hρ A
    have hWeak : Renaming Γ (Δ.snoc (A.rename ρ)) (Fin.succ ∘ ρ) :=
      renaming_comp hρ (renaming_weaken Δ (A.rename ρ))
    have hAWeak : Derivation (Δ.snoc (A.rename ρ)) (A.rename ρ).weaken (.univ i) := by
      simpa only [Term.weaken, Term.rename, Term.rename_comp] using ihA hExt _ hWeak
    have haWeak : Derivation (Δ.snoc (A.rename ρ)) (a.rename ρ).weaken (A.rename ρ).weaken := by
      simpa only [Term.weaken, Term.rename, Term.rename_comp] using iha hExt _ hWeak
    have hId := Derivation.id hAWeak haWeak (Derivation.var hExt Lookup.here)
    have hρ'' : Renaming (motiveContext Γ A a) _ (Term.upRen (Term.upRen ρ)) :=
      renaming_lift hρ' (.id A.weaken a.weaken (.var 0))
    simp only [Term.rename, rename_weaken] at hρ''
    simpa only [Term.rename, rename_instantiate₂] using
      Derivation.j hA' ha'
        (ihC (.snoc hExt hId) _ hρ'')
        (by simpa only [Term.rename, rename_instantiate₂] using ihd hΔ ρ hρ)
        (ihb hΔ ρ hρ) (ihp hΔ ρ hρ)
  | conv ht hB hAB iht ihB =>
    exact .conv (iht hΔ ρ hρ) (ihB hΔ ρ hρ) (conversion_rename hAB ρ)
  | cumulative hA hij ihA => exact .cumulative (ihA hΔ ρ hρ) hij


noncomputable def substitution_lift {n m i : ℕ} {Γ : Context n} {Δ : Context m}
    {σ : Fin n → Term m} {A : Term n} (hσ : Substitution Γ Δ σ)
    (hΔ : ContextDerivation Δ) (hA : Derivation Δ (A.subst σ) (.univ i)) :
    Substitution (Γ.snoc A) (Δ.snoc (A.subst σ)) (Term.upSub σ) := by
  intro j B hj
  apply Classical.choice
  cases hj with
  | here =>
    rw [subst_weaken]
    exact ⟨.var (.snoc hΔ hA) .here⟩
  | there hj =>
    rw [subst_weaken]
    exact ⟨derivation_rename (hσ hj) (.snoc hΔ hA) Fin.succ (renaming_weaken _ _)⟩

theorem subst_natStepType {n m : ℕ} (C : Term (n + 1)) (σ : Fin n → Term m) :
    C.natStepType.subst σ = (C.subst (Term.upSub σ)).natStepType := by
  simp only [Term.natStepType, Term.subst, Term.subst_comp]
  congr 3
  funext i
  cases i using Fin.cases with
  | zero => rfl
  | succ i =>
    change ((σ i).rename Fin.succ).rename Fin.succ = ((σ i).rename Fin.succ).subst _
    rw [Term.subst_rename, Term.rename_comp]
    exact (Term.subst_renaming (σ i) (Fin.succ ∘ Fin.succ)).symm

noncomputable def derivation_subst {n : ℕ} {Γ : Context n} {t A : Term n}
    (h : Derivation Γ t A) {m : ℕ} {Δ : Context m} (hΔ : ContextDerivation Δ)
    (σ : Fin n → Term m) (hσ : Substitution Γ Δ σ) :
    Derivation Δ (t.subst σ) (A.subst σ) := by
  induction h using Derivation.rec (motive_1 := fun _ _ => PUnit) generalizing m with
  | nil => exact ⟨⟩
  | snoc _ _ _ _ => exact ⟨⟩
  | univ _ i _ => exact .univ hΔ i
  | nat _ _ => exact .nat hΔ
  | empty _ _ => exact .empty hΔ
  | unit _ _ => exact .unit hΔ
  | var _ hi _ => exact hσ hi
  | pi hA hB ihA ihB =>
    exact .pi (ihA hΔ σ hσ)
      (ihB (.snoc hΔ (ihA hΔ σ hσ)) _ (substitution_lift hσ hΔ (ihA hΔ σ hσ)))
  | sigma hA hB ihA ihB =>
    exact .sigma (ihA hΔ σ hσ)
      (ihB (.snoc hΔ (ihA hΔ σ hσ)) _ (substitution_lift hσ hΔ (ihA hΔ σ hσ)))
  | lam hA hB ht ihA ihB iht =>
    exact .lam (ihA hΔ σ hσ)
      (ihB (.snoc hΔ (ihA hΔ σ hσ)) _ (substitution_lift hσ hΔ (ihA hΔ σ hσ)))
      (iht (.snoc hΔ (ihA hΔ σ hσ)) _ (substitution_lift hσ hΔ (ihA hΔ σ hσ)))
  | app hf ha ihf iha =>
    simpa only [Term.subst, subst_instantiate] using
      Derivation.app (ihf hΔ σ hσ) (iha hΔ σ hσ)
  | pair hA hB ha hb ihA ihB iha ihb =>
    apply Derivation.pair (ihA hΔ σ hσ)
      (ihB (.snoc hΔ (ihA hΔ σ hσ)) _ (substitution_lift hσ hΔ (ihA hΔ σ hσ)))
      (iha hΔ σ hσ)
    simpa only [subst_instantiate] using ihb hΔ σ hσ
  | fst hp ihp => exact .fst (ihp hΔ σ hσ)
  | snd hp ihp =>
    simpa only [Term.subst, subst_instantiate] using Derivation.snd (ihp hΔ σ hσ)
  | zero _ _ => exact .zero hΔ
  | succ ht iht => exact .succ (iht hΔ σ hσ)
  | natrec hC hz hs ht ihC ihz ihs iht =>
    have hNat := Derivation.nat hΔ
    simpa only [Term.subst, subst_instantiate] using
      Derivation.natrec
        (ihC (.snoc hΔ hNat) _ (substitution_lift (A := .nat) hσ hΔ hNat))
        (by simpa only [Term.subst, subst_instantiate] using ihz hΔ σ hσ)
        (by simpa only [subst_natStepType] using ihs hΔ σ hσ)
        (iht hΔ σ hσ)
  | star _ _ => exact .star hΔ
  | absurd hA he ihA ihe => exact .absurd (ihA hΔ σ hσ) (ihe hΔ σ hσ)
  | id hA ha hb ihA iha ihb => exact .id (ihA hΔ σ hσ) (iha hΔ σ hσ) (ihb hΔ σ hσ)
  | refl hA ha ihA iha => exact .refl (ihA hΔ σ hσ) (iha hΔ σ hσ)
  | j hA ha hC hd hb hp ihA iha ihC ihd ihb ihp =>
    rename_i n i j Γ A a d b p C
    have hA' := ihA hΔ σ hσ
    have ha' := iha hΔ σ hσ
    have hExt := ContextDerivation.snoc hΔ hA'
    have hσ' : Substitution (Γ.snoc A) _ (Term.upSub σ) := substitution_lift hσ hΔ hA'
    have hAWeak := derivation_rename hA' hExt Fin.succ (renaming_weaken _ _)
    have haWeak := derivation_rename ha' hExt Fin.succ (renaming_weaken _ _)
    have hId := Derivation.id hAWeak haWeak (Derivation.var hExt Lookup.here)
    have hσ'' : Substitution (motiveContext Γ A a) _ (Term.upSub (Term.upSub σ)) :=
      substitution_lift (A := .id A.weaken a.weaken (.var 0)) hσ' hExt
        (by
          change Derivation _ (.id (A.weaken.subst (Term.upSub σ))
            (a.weaken.subst (Term.upSub σ)) (.var 0)) (.univ i)
          rw [subst_weaken, subst_weaken]
          exact hId)
    simp only [Term.subst, subst_weaken] at hσ''
    simpa only [Term.subst, subst_instantiate₂] using
      Derivation.j hA' ha'
        (ihC (.snoc hExt hId) _ hσ'')
        (by simpa only [Term.subst, subst_instantiate₂] using ihd hΔ σ hσ)
        (ihb hΔ σ hσ) (ihp hΔ σ hσ)
  | conv ht hB hAB iht ihB =>
    exact .conv (iht hΔ σ hσ) (ihB hΔ σ hσ) (conversion_subst hAB σ)
  | cumulative hA hij ihA => exact .cumulative (ihA hΔ σ hσ) hij

noncomputable def substitution_id {n : ℕ} {Γ : Context n} (hΓ : ContextDerivation Γ) :
    Substitution Γ Γ Term.var := by
  intro i A hi
  simpa only [Term.subst_var] using Derivation.var hΓ hi

noncomputable def substitution_cons {n m : ℕ} {Γ : Context n} {Δ : Context m}
    {σ : Fin n → Term m} {A : Term n} {a : Term m}
    (hσ : Substitution Γ Δ σ) (ha : Derivation Δ a (A.subst σ)) :
    Substitution (Γ.snoc A) Δ (Fin.cons a σ) := by
  intro i B hi
  apply Classical.choice
  cases hi with
  | here =>
    change Nonempty (Derivation Δ a ((A.rename Fin.succ).subst (Fin.cons a σ)))
    rw [Term.subst_rename]
    exact ⟨ha⟩
  | there hi =>
    simp only [Term.weaken, Term.subst_rename]
    exact ⟨hσ hi⟩

noncomputable def derivation_instantiate {n : ℕ} {Γ : Context n} {A a : Term n}
    {t B : Term (n + 1)} (ht : Derivation (Γ.snoc A) t B)
    (hΓ : ContextDerivation Γ) (ha : Derivation Γ a A) :
    Derivation Γ (t.instantiate a) (B.instantiate a) := by
  have ha' : Derivation Γ a (A.subst Term.var) := by simpa only [Term.subst_var] using ha
  exact derivation_subst ht hΓ _ (substitution_cons (substitution_id hΓ) ha')

theorem typedEq_subst {n m : ℕ} {Γ : Context n} {Δ : Context m} {t u A : Term n}
    (h : TypedEq Γ t u A) (hΔ : ContextDerivation Δ) (σ : Fin n → Term m)
    (hσ : Substitution Γ Δ σ) : TypedEq Δ (t.subst σ) (u.subst σ) (A.subst σ) := by
  obtain ⟨⟨ht⟩, ⟨hu⟩, ⟨hconv⟩⟩ := h
  exact ⟨⟨derivation_subst ht hΔ σ hσ⟩, ⟨derivation_subst hu hΔ σ hσ⟩,
    ⟨conversion_subst hconv σ⟩⟩

end Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.Substitution
