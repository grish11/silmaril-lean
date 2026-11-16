module

public import Silmaril.Logic.TypeTheory.LambdaPi.TypedEquality.EqualSubstitution.Defs

public section
namespace Silmaril.Proofs.Logic.TypeTheory.LambdaPi.TypedEqualityEqualSubstitution
open Silmaril.Logic.TypeTheory.IntensionalMLTT
open Silmaril.Logic.TypeTheory.LambdaPi.TypedEquality

theorem left {n l m : ℕ} {Γ : Context n} {T : Context l} {Δ : Context m}
    {σ τ : Fin n → Term m} (h : EqualSubstitution Γ T Δ σ τ) : TypedSubstitution Γ T Δ σ := by
  intro i A hi
  exact .trans (h hi) (.symm (h hi))

theorem diagonal {n l m : ℕ} {Γ : Context n} {T : Context l} {Δ : Context m}
    {σ : Fin n → Term m} (h : TypedSubstitution Γ T Δ σ) : EqualSubstitution Γ T Δ σ σ := h

theorem cons {n l m : ℕ} {Γ : Context n} {T : Context l} {Δ : Context m}
    {σ τ : Fin n → Term m} {A : Term n} {a a' : Term m}
    (h : EqualSubstitution Γ T Δ σ τ) (ha : Equality T Δ a a' (A.subst σ)) :
    EqualSubstitution (Γ.snoc A) T Δ (Fin.cons a σ) (Fin.cons a' τ) := by
  intro i B hi
  cases hi with
  | here =>
    change Equality T Δ a a' ((A.rename Fin.succ).subst (Fin.cons a σ))
    rw [Term.subst_rename]
    exact ha
  | there hi =>
    simpa only [Term.weaken, Term.subst_rename, Function.comp_def, Fin.cons_succ] using h hi

theorem lift {n l m : ℕ} {Γ : Context n} {T : Context l} {Δ : Context m}
    {σ τ : Fin n → Term m} {A : Term n} (h : EqualSubstitution Γ T Δ σ τ)
    (hA : Equality T Δ (A.subst σ) (A.subst σ) (.univ 0)) :
    EqualSubstitution (Γ.snoc A) T (Δ.snoc (A.subst σ)) (Term.upSub σ) (Term.upSub τ) := by
  intro i B hi
  cases hi with
  | here =>
    rw [Term.subst_weaken]
    exact .var (.snoc hA.context hA) .here
  | there hi =>
    rw [Term.subst_weaken]
    exact (h hi).weaken hA

private theorem instantiate_subst {n m : ℕ} (t : Term (n + 1)) (a : Term n)
    (σ : Fin n → Term m) :
    (t.instantiate a).subst σ = t.subst (Fin.cons (a.subst σ) σ) := by
  simp only [Term.instantiate, Term.subst_comp]
  congr 1
  funext i
  cases i using Fin.cases <;> rfl

private theorem instantiate_fresh {n : ℕ} (t : Term (n + 1)) :
    (t.rename (Term.upRen Fin.succ)).instantiate (.var 0) = t := by
  change (t.rename (Term.upRen Fin.succ)).subst (Fin.cons (.var 0) Term.var) = t
  rw [Term.subst_rename]
  have he : (Fin.cons (.var 0) Term.var) ∘ Term.upRen Fin.succ =
      (Term.var : Fin (n + 1) → Term (n + 1)) := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  rw [he, Term.subst_var]

private theorem fresh_app {k n : ℕ} {S : Context k} {Γ : Context n}
    {A f g : Term n} {B : Term (n + 1)} {s : LFSort}
    (hA : Equality S Γ A A (.univ 0))
    (hB : Equality S (Γ.snoc A) B B (.univ s.val))
    (hf : Equality S Γ f g (.pi A B)) :
    Equality S (Γ.snoc A) (.app f.weaken (.var 0)) (.app g.weaken (.var 0)) B := by
  have hAw := hA.weaken hA
  have hΔ := ContextFormed.snoc (ContextFormed.snoc hA.context hA) hAw
  have hBw : Equality S ((Γ.snoc A).snoc A.weaken)
      (B.rename (Term.upRen Fin.succ)) (B.rename (Term.upRen Fin.succ)) (.univ s.val) :=
    hB.rename hΔ (Term.upRen Fin.succ) (Renaming.lift (Renaming.weaken Γ A) A)
  have hv : Equality S (Γ.snoc A) (.var 0) (.var 0) A.weaken :=
    .var (.snoc hA.context hA) .here
  simpa only [Term.weaken, Term.rename, instantiate_fresh] using
    Equality.app hAw hBw (hf.weaken hA) hv

/-- Tracking each endpoint separately makes symmetry and transitivity preserve
the original left carrier. Source formation premises justify dependent application transport. -/
theorem endpoints {k n : ℕ} {S : Context k} {Γ : Context n} {t u C : Term n}
    (h : Equality S Γ t u C) {l m : ℕ} {T : Context l} {Δ : Context m}
    (hΔ : ContextFormed T Δ) (σ τ : Fin n → Term m) (hστ : EqualSubstitution Γ T Δ σ τ) :
    Equality T Δ (t.subst σ) (t.subst τ) (C.subst σ) ∧
      Equality T Δ (u.subst σ) (u.subst τ) (C.subst σ) := by
  induction h using Equality.rec (motive_1 := fun _ _ => True)
      (motive_2 := fun _ _ _ _ => True) generalizing l m
  case nil => trivial
  case snoc => trivial
  case signature => trivial
  case snoc => intros; trivial
  case type => exact ⟨.type hΔ, .type hΔ⟩
  case var _ hi _ => exact ⟨hστ hi, hστ hi⟩
  case pi k n S s Γ A A' B B' hA hB ihA ihB =>
    show Equality T Δ ((Term.pi A B).subst σ) ((Term.pi A B).subst τ) (.univ s.val) ∧
      Equality T Δ ((Term.pi A' B').subst σ) ((Term.pi A' B').subst τ) (.univ s.val)
    have hAσ : Equality T Δ (A.subst σ) (A'.subst σ) (.univ 0) := hA.subst hΔ σ (left hστ)
    have hAf : Equality T Δ (A.subst σ) (A.subst σ) (.univ 0) := .trans hAσ (.symm hAσ)
    have hExt : EqualSubstitution (Γ.snoc A) T (Δ.snoc (A.subst σ)) (Term.upSub σ) (Term.upSub τ) := lift hστ hAf
    have bodies := ihB (.snoc hΔ hAf) _ _ hExt
    exact ⟨.pi (ihA hΔ σ τ hστ).1 bodies.1,
      .pi (ihA hΔ σ τ hστ).2 (bodies.2.convertLast hAσ)⟩
  case lam k n S s Γ A B b b' hA hB hb ihA ihB ihb =>
    show Equality T Δ ((Term.lam A b).subst σ) ((Term.lam A b).subst τ) ((Term.pi A B).subst σ) ∧
      Equality T Δ ((Term.lam A b').subst σ) ((Term.lam A b').subst τ) ((Term.pi A B).subst σ)
    have hAσ : Equality T Δ (A.subst σ) (A.subst σ) (.univ 0) := hA.subst hΔ σ (left hστ)
    have hExt : EqualSubstitution (Γ.snoc A) T (Δ.snoc (A.subst σ)) (Term.upSub σ) (Term.upSub τ) := lift hστ hAσ
    have hBσ := hB.subst (.snoc hΔ hAσ) _ (left hExt)
    have bodies := ihb (.snoc hΔ hAσ) _ _ hExt
    exact ⟨Equality.lamCongr (ihA hΔ σ τ hστ).1 hBσ bodies.1,
      Equality.lamCongr (ihA hΔ σ τ hστ).1 hBσ bodies.2⟩
  case app k n S s Γ A f f' a a' B hA hB hf ha ihA ihB ihf iha =>
    show Equality T Δ ((Term.app f a).subst σ) ((Term.app f a).subst τ) ((B.instantiate a).subst σ) ∧
      Equality T Δ ((Term.app f' a').subst σ) ((Term.app f' a').subst τ) ((B.instantiate a).subst σ)
    have hAσ : Equality T Δ (A.subst σ) (A.subst σ) (.univ 0) := hA.subst hΔ σ (left hστ)
    have hExt : EqualSubstitution (Γ.snoc A) T (Δ.snoc (A.subst σ)) (Term.upSub σ) (Term.upSub τ) := lift hστ hAσ
    have hBσ := hB.subst (.snoc hΔ hAσ) _ (left hExt)
    have functions := ihf hΔ σ τ hστ
    have arguments := iha hΔ σ τ hστ
    have originalArgs := ha.subst hΔ σ (left hστ)
    have hArgs : EqualSubstitution (Γ.snoc A) T Δ
        (Fin.cons (a.subst σ) σ) (Fin.cons (a'.subst σ) σ) :=
      cons (diagonal (left hστ)) originalArgs
    have carriers : Equality T Δ (B.subst (Fin.cons (a.subst σ) σ))
        (B.subst (Fin.cons (a'.subst σ) σ)) (.univ s.val) := (ihB hΔ _ _ hArgs).1
    constructor
    · simpa only [Term.subst, Term.subst_instantiate] using
        Equality.app hAσ hBσ functions.1 arguments.1
    · have result := Equality.app hAσ hBσ functions.2 arguments.2
      have carrier : Equality T Δ
          ((B.subst (Term.upSub σ)).instantiate (a.subst σ))
          ((B.subst (Term.upSub σ)).instantiate (a'.subst σ)) (.univ s.val) := by
        simpa only [← instantiate_subst, Term.subst_instantiate] using carriers
      simpa only [Term.subst, Term.subst_instantiate] using Equality.conv result (.symm carrier)
  case beta k n S s Γ A a B b hA hB hb ha ihA ihB ihb iha =>
    show Equality T Δ ((Term.app (.lam A b) a).subst σ) ((Term.app (.lam A b) a).subst τ)
        ((B.instantiate a).subst σ) ∧
      Equality T Δ ((b.instantiate a).subst σ) ((b.instantiate a).subst τ) ((B.instantiate a).subst σ)
    have hAσ : Equality T Δ (A.subst σ) (A.subst σ) (.univ 0) := hA.subst hΔ σ (left hστ)
    have hExt : EqualSubstitution (Γ.snoc A) T (Δ.snoc (A.subst σ)) (Term.upSub σ) (Term.upSub τ) := lift hστ hAσ
    have hBσ := hB.subst (.snoc hΔ hAσ) _ (left hExt)
    have body := (ihb (.snoc hΔ hAσ) _ _ hExt).1
    have args := (iha hΔ σ τ hστ).1
    have funcs := Equality.lamCongr (ihA hΔ σ τ hστ).1 hBσ body
    have replacements : EqualSubstitution (Γ.snoc A) T Δ
        (Fin.cons (a.subst σ) σ) (Fin.cons (a.subst τ) τ) := cons hστ args
    constructor
    · simpa only [Term.subst, Term.subst_instantiate] using Equality.app hAσ hBσ funcs args
    · simpa only [instantiate_subst] using (ihb hΔ _ _ replacements).1
  case eta k n S s Γ A f B hA hB hf ihA ihB ihf =>
    show Equality T Δ ((Term.lam A (.app f.weaken (.var 0))).subst σ)
        ((Term.lam A (.app f.weaken (.var 0))).subst τ) ((Term.pi A B).subst σ) ∧
      Equality T Δ (f.subst σ) (f.subst τ) ((Term.pi A B).subst σ)
    have hAσ : Equality T Δ (A.subst σ) (A.subst σ) (.univ 0) := hA.subst hΔ σ (left hστ)
    have hExt : EqualSubstitution (Γ.snoc A) T (Δ.snoc (A.subst σ)) (Term.upSub σ) (Term.upSub τ) := lift hστ hAσ
    have hBσ := hB.subst (.snoc hΔ hAσ) _ (left hExt)
    have functions := (ihf hΔ σ τ hστ).1
    have body := fresh_app hAσ hBσ functions
    have abstraction := Equality.lamCongr (ihA hΔ σ τ hστ).1 hBσ body
    have hzσ : Term.upSub σ 0 = .var 0 := rfl
    have hzτ : Term.upSub τ 0 = .var 0 := rfl
    exact ⟨by simpa only [Term.subst, Term.subst_weaken, hzσ, hzτ] using abstraction, functions⟩
  case conv k n S s Γ t u A B ht hAB iht _ =>
    have carrier := hAB.subst hΔ σ (left hστ)
    exact ⟨.conv (iht hΔ σ τ hστ).1 carrier, .conv (iht hΔ σ τ hστ).2 carrier⟩
  case symm _ ih => exact (ih hΔ σ τ hστ).symm
  case trans _ _ ih ik => exact ⟨(ih hΔ σ τ hστ).1, (ik hΔ σ τ hστ).2⟩

end Silmaril.Proofs.Logic.TypeTheory.LambdaPi.TypedEqualityEqualSubstitution
