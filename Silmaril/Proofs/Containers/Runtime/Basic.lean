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
    ((R.enforce Pr).beh i).Sat (Spec.always fun e => Pr e.cap = true) := by
  intro b hb
  cases hl : R.load i with
  | error r =>
    rw [(beh_error (R := R.enforce Pr) hl b).1 hb]
    exact always_done_nil _
  | ok p =>
    obtain ⟨b₀, -, b₁, -, he⟩ := (beh_ok (R := R.enforce Pr) hl b).1 hb
    rcases he with ⟨ha, rfl⟩ | ⟨t, e, -, hc, -, rfl⟩
    · exact ha
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
      rcases he with ⟨-, rfl⟩ | ⟨t, e, hp, -, hf, -⟩
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

/-- **Enforcement keeps undefined behaviour that is reached**: a run of `R` with undefined
behaviour all of whose events the profile allows is a run of the enforced model. -/
theorem enforce_keeps_reached_ub {R : Runtime I P Ev} {Pr : Profile} {i : I} {b : Beh Ev}
    (hb : R.beh i b) (ha : Spec.always (fun e => Pr e.cap = true) b) :
    (R.enforce Pr).beh i b := by
  cases hl : R.load i with
  | error r => exact (beh_error (R := R.enforce Pr) hl b).2 ((beh_error hl b).1 hb)
  | ok p =>
    obtain ⟨b₀, hs, ho⟩ := (beh_ok hl b).1 hb
    exact (beh_ok (R := R.enforce Pr) hl b).2 ⟨b₀, hs, b, ho, .inl ⟨ha, rfl⟩⟩

/-- **Enforcement removes undefined behaviour only by pre-emption**: if no run of the enforced
model has undefined behaviour, every run of `R` with undefined behaviour has a disallowed event
(which comes before the undefined behaviour that ends the run). -/
theorem ub_preempted_of_enforce {R : Runtime I P Ev} {Pr : Profile} {i : I}
    (h : ((R.enforce Pr).beh i).Sat Spec.noUB) {b : Beh Ev} (hb : R.beh i b)
    (hu : ¬ Spec.noUB b) : ¬ Spec.always (fun e => Pr e.cap = true) b :=
  fun ha => hu (h b (enforce_keeps_reached_ub hb ha))

/-- **An arbitrary account of what the runtime adds can hide undefined behaviour.** -/
theorem withObs_can_hide_ub :
    ∃ (R : Runtime Unit Unit Unit) (o : Beh Unit → Beh Unit → Prop),
      ¬ (R.beh ()).Sat Spec.noUB ∧ ((R.withObs o).beh ()).Sat Spec.noUB := by
  refine ⟨Runtime.exact (fun _ => .ok ()) (fun _ b => b = .done [] (.undefined .other)),
    fun b₀ b => b₀ = b ∧ Spec.noUB b, ?_, ?_⟩
  · intro h
    exact h _ ((beh_ok rfl _).2 ⟨_, rfl, rfl⟩)
  · intro b hb
    obtain ⟨_, -, -, h⟩ := (beh_ok (R := Runtime.withObs _ _) rfl b).1 hb
    exact h

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
    rcases he with ⟨-, rfl⟩ | ⟨t, -, -, -, -, rfl⟩
    · exact .inl h₁
    · exact .inr ⟨t, .policy, rfl⟩

/-- A program run with undefined behaviour is a run the environment sees, when what the
runtime adds keeps undefined behaviour. -/
theorem beh_of_sem_undefined {R : Runtime I P E} (hobs : Runtime.ObsKeepsUB R.obs) {i : I}
    {p : P} (hl : R.load i = .ok p) {b : Beh E} (hs : R.sem p b) (hu : ¬ Spec.noUB b) :
    R.beh i b :=
  (beh_ok hl b).2 ⟨b, hs, hobs b hu⟩

end Silmaril.Proofs.Containers.Runtime
