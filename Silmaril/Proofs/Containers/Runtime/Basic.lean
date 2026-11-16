module

public import Silmaril.Containers.Runtime.Defs

/-!
# Proofs: runtime models

Proofs for `Silmaril.Containers.Runtime.Thms`. Nothing imports this module except that header.
-/

@[expose] public section

namespace Silmaril.Proofs.Containers.Runtime

open Silmaril.Containers

variable {I P E : Type}

theorem prefix_of_prefix {b : Beh E} {t u : List E} (h : b.Prefix t) (hu : u <+: t) :
    b.Prefix u := by
  cases b with
  | done t' s => exact hu.trans h
  | blocked t' => exact hu.trans h
  | spins t' => exact hu.trans h
  | reactive f =>
    simp only [Beh.Prefix] at h ⊢
    have hl : u.length ≤ t.length := hu.length_le
    rw [h] at hu
    calc u = (List.map f (List.range t.length)).take u.length := List.prefix_iff_eq_take.1 hu
      _ = List.map f ((List.range t.length).take u.length) := (List.map_take ..).symm
      _ = List.map f (List.range u.length) := by rw [List.take_range, Nat.min_eq_left hl]

theorem beh_error {R : Runtime I P E} {i : I} {r : Refusal} (hl : R.load i = .error r)
    (b : Beh E) : R.beh i b ↔ b = .done [] (.refused r) := by
  simp only [Runtime.beh, hl]

theorem beh_ok {R : Runtime I P E} {i : I} {p : P} (hl : R.load i = .ok p) (b : Beh E) :
    R.beh i b ↔ ∃ b₀, R.sem p b₀ ∧ R.obs b₀ b := by
  simp only [Runtime.beh, hl]

/-- Replacing what the runtime adds by less gives a smaller model. -/
theorem le_withObs {R : Runtime I P E} {o : Beh E → Beh E → Prop}
    (h : ∀ b₀ b, o b₀ b → R.obs b₀ b) :
    (R.withObs o).Le R := by
  intro i b hb
  cases hl : R.load i with
  | error r => exact (beh_error hl b).2 ((beh_error (R := R.withObs o) hl b).1 hb)
  | ok p =>
    obtain ⟨b₀, hs, ho⟩ := (beh_ok (R := R.withObs o) hl b).1 hb
    exact (beh_ok hl b).2 ⟨b₀, hs, h b₀ b ho⟩

theorem restrict_le (R : Runtime I P E) (A : Spec E) : (R.restrict A).Le R :=
  le_withObs fun _ _ h => h.1

theorem le_mayKill (R : Runtime I P E) (ks : Kill → Prop) : R.Le (R.mayKill ks) := by
  intro i b hb
  cases hl : R.load i with
  | error r => exact (beh_error (R := R.mayKill ks) hl b).2 ((beh_error hl b).1 hb)
  | ok p =>
    obtain ⟨b₀, hs, ho⟩ := (beh_ok hl b).1 hb
    exact (beh_ok (R := R.mayKill ks) hl b).2 ⟨b₀, hs, b, ho, .inl rfl⟩

/-- The runs of `R.mayKill ks`: a run of `R`, or a prefix of one followed by a kill. -/
theorem beh_mayKill {R : Runtime I P E} {ks : Kill → Prop} {i : I} {b : Beh E}
    (hb : (R.mayKill ks).beh i b) :
    R.beh i b ∨ ∃ b₁ t k, R.beh i b₁ ∧ ks k ∧ b₁.Prefix t ∧ b = .done t (.killed k) := by
  cases hl : R.load i with
  | error r => exact .inl ((beh_error hl b).2 ((beh_error (R := R.mayKill ks) hl b).1 hb))
  | ok p =>
    obtain ⟨b₀, hs, b₁, ho, hk⟩ := (beh_ok (R := R.mayKill ks) hl b).1 hb
    have h₁ : R.beh i b₁ := (beh_ok hl b₁).2 ⟨b₀, hs, ho⟩
    rcases hk with rfl | ⟨t, k, hk, hp, rfl⟩
    · exact .inl h₁
    · exact .inr ⟨b₁, t, k, h₁, hk, hp, rfl⟩

theorem safe_mayKill {R : Runtime I P E} {ks : Kill → Prop} {i : I} {S : List E → Prop}
    (h : (R.beh i).Sat (Spec.safe S)) : ((R.mayKill ks).beh i).Sat (Spec.safe S) := by
  intro b hb u hu
  rcases beh_mayKill hb with h₁ | ⟨b₁, t, k, h₁, -, hp, rfl⟩
  · exact h b h₁ u hu
  · exact h b₁ h₁ u (prefix_of_prefix hp hu)

theorem partialCorrect_mayKill {R : Runtime I P E} {ks : Kill → Prop} {i : I}
    {post : List E → UInt8 → Prop} (h : (R.beh i).Sat (Spec.partialCorrect post)) :
    ((R.mayKill ks).beh i).Sat (Spec.partialCorrect post) := by
  intro b hb
  rcases beh_mayKill hb with h₁ | ⟨b₁, t, k, h₁, -, hp, rfl⟩
  · exact h b h₁
  · trivial

theorem totalCorrect_not_mayKill :
    ∃ R : Runtime Unit Unit Unit,
      (R.beh ()).Sat (Spec.totalCorrect fun _ _ => True) ∧
        ¬ ((R.mayKill (· = .oom)).beh ()).Sat (Spec.totalCorrect fun _ _ => True) := by
  refine ⟨Runtime.exact (fun _ => .ok ()) (fun _ b => b = .done [] (.exited 0)), ?_, ?_⟩
  · intro b hb
    obtain ⟨b₀, rfl, rfl⟩ := (beh_ok rfl b).1 hb
    trivial
  · intro h
    exact h (.done [] (.killed .oom))
      ((beh_ok rfl _).2 ⟨_, rfl, _, rfl, .inr ⟨[], .oom, rfl, List.nil_prefix, rfl⟩⟩)

theorem always_done_nil {ok : E → Prop} (s : Stop) : Spec.always ok (.done [] s) := by
  intro u hu e he
  rw [List.eq_nil_of_prefix_nil hu] at he
  cases he

theorem enforce_confined {R : Runtime I P Ev} {Pr : Profile} {i : I} :
    ((R.enforce Pr).beh i).Sat
      (Spec.under Spec.noUB (Spec.always fun e => Pr e.cap = true)) := by
  intro b hb hnu
  cases hl : R.load i with
  | error r =>
    rw [(beh_error (R := R.enforce Pr) hl b).1 hb]
    exact always_done_nil _
  | ok p =>
    obtain ⟨b₀, -, b₁, -, he⟩ := (beh_ok (R := R.enforce Pr) hl b).1 hb
    rcases he with ⟨ha, rfl⟩ | ⟨hu, rfl⟩ | ⟨t, e, -, hc, -, rfl⟩
    · exact ha
    · exact (hu hnu).elim
    · intro u hu x hx
      exact hc x (hu.subset hx)

theorem enforce_eq_of_confined {R : Runtime I P Ev} {Pr : Profile} {i : I}
    (h : (R.beh i).Sat (Spec.always fun e => Pr e.cap = true)) (b : Beh Ev) :
    (R.enforce Pr).beh i b ↔ R.beh i b := by
  cases hl : R.load i with
  | error r => rw [beh_error hl, beh_error (R := R.enforce Pr) hl]
  | ok p =>
    rw [beh_ok hl, beh_ok (R := R.enforce Pr) hl]
    constructor
    · rintro ⟨b₀, hs, b₁, ho, he⟩
      have ha := h b₁ ((beh_ok hl b₁).2 ⟨b₀, hs, ho⟩)
      rcases he with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨t, e, hp, -, hf, -⟩
      · exact ⟨b₀, hs, ho⟩
      · exact ⟨b₀, hs, ho⟩
      · have h' : Pr e.cap = true := ha (t ++ [e]) hp e (by simp)
        rw [hf] at h'; cases h'
    · rintro ⟨b₀, hs, ho⟩
      exact ⟨b₀, hs, b, ho, .inl ⟨h b ((beh_ok hl b).2 ⟨b₀, hs, ho⟩), rfl⟩⟩

/-! ## Undefined behaviour is preserved -/

/-- A transformer of what the runtime adds that keeps every run (with or without undefined
behaviour) preserves the undefined behaviour of the model. -/
theorem preservesUB_withObs {R : Runtime I P E} {o : Beh E → Beh E → Prop}
    (h : ∀ b₀ b, R.obs b₀ b → ¬ Spec.noUB b → o b₀ b) : (R.withObs o).PreservesUB R := by
  intro i b hb hu
  cases hl : R.load i with
  | error r => exact (beh_error (R := R.withObs o) hl b).2 ((beh_error hl b).1 hb)
  | ok p =>
    obtain ⟨b₀, hs, ho⟩ := (beh_ok hl b).1 hb
    exact (beh_ok (R := R.withObs o) hl b).2 ⟨b₀, hs, h b₀ b ho hu⟩

theorem preservesUB_restrict (R : Runtime I P E) (A : Spec E) : (R.restrict A).PreservesUB R :=
  preservesUB_withObs fun _ _ ho hu => ⟨ho, .inr hu⟩

theorem preservesUB_mayKill (R : Runtime I P E) (ks : Kill → Prop) :
    (R.mayKill ks).PreservesUB R :=
  preservesUB_withObs fun _ b ho _ => ⟨b, ho, .inl rfl⟩

theorem preservesUB_enforce (R : Runtime I P Ev) (Pr : Profile) :
    (R.enforce Pr).PreservesUB R :=
  preservesUB_withObs fun _ b ho hu => ⟨b, ho, .inr (.inl ⟨hu, rfl⟩)⟩

theorem noUB_of_preservesUB {P' : Type} {R' : Runtime I P' E} {R : Runtime I P E}
    (h : R'.PreservesUB R) {i : I} (h' : (R'.beh i).Sat Spec.noUB) : (R.beh i).Sat Spec.noUB := by
  intro b hb
  by_cases hu : Spec.noUB b
  · exact hu
  · exact h' b (h i b hb hu)

/-- The runs of a model whose runtime additions are only kills or stops of runs of `R`. -/
theorem noUB_of_runs {P' : Type} {R' : Runtime I P' E} {R : Runtime I P E} {i : I}
    (h : ∀ b, R'.beh i b → R.beh i b ∨ ∃ t k, b = .done t (.killed k))
    (hR : (R.beh i).Sat Spec.noUB) : (R'.beh i).Sat Spec.noUB := by
  intro b hb
  rcases h b hb with h₁ | ⟨t, k, rfl⟩
  · exact hR b h₁
  · trivial

theorem enforce_runs {R : Runtime I P Ev} {Pr : Profile} {i : I} {b : Beh Ev}
    (hb : (R.enforce Pr).beh i b) : R.beh i b ∨ ∃ t k, b = .done t (.killed k) := by
  cases hl : R.load i with
  | error r => exact .inl ((beh_error hl b).2 ((beh_error (R := R.enforce Pr) hl b).1 hb))
  | ok p =>
    obtain ⟨b₀, hs, b₁, ho, he⟩ := (beh_ok (R := R.enforce Pr) hl b).1 hb
    have h₁ : R.beh i b₁ := (beh_ok hl b₁).2 ⟨b₀, hs, ho⟩
    rcases he with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨t, -, -, -, -, rfl⟩
    · exact .inl h₁
    · exact .inl h₁
    · exact .inr ⟨t, .policy, rfl⟩

/-- A program run with undefined behaviour is a run the environment sees, when what the
runtime adds keeps undefined behaviour. -/
theorem beh_of_sem_undefined {R : Runtime I P E} (hobs : Runtime.ObsKeepsUB R.obs) {i : I}
    {p : P} (hl : R.load i = .ok p) {b : Beh E} (hs : R.sem p b) (hu : ¬ Spec.noUB b) :
    R.beh i b :=
  (beh_ok hl b).2 ⟨b, hs, hobs b hu⟩

end Silmaril.Proofs.Containers.Runtime
