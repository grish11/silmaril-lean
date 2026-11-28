module

public import Silmaril.Logic.Temporal.TLA.Defs

public section

namespace Silmaril.Proofs.Logic.Temporal.TLA

open Silmaril.Logic.Temporal.TLA

universe u

variable {S V W : Type u}

theorem holds_suffix (p : Formula S) (σ : Behavior S) (n i : Nat) :
    p.Holds (σ.suffix n) i ↔ p.Holds σ (n + i) := by
  induction p generalizing i with
  | state => rfl
  | alwaysBracket A f =>
    simp only [Formula.Holds, Behavior.suffix, ← Nat.add_assoc]
    constructor
    · intro h j hj
      have he : n + (j - n) = j := by omega
      simpa only [he] using h (j - n) (by omega)
    · intro h j hj
      exact h (n + j) (by omega)
  | neg _ ih => exact not_congr (ih σ i)
  | conj _ _ ihp ihq => exact and_congr (ihp σ i) (ihq σ i)
  | always p ih =>
    constructor
    · intro h j hj
      have he : n + (j - n) = j := by omega
      simpa only [he] using (ih σ (j - n)).mp (h (j - n) (by omega))
    · intro h j hj
      exact (ih σ j).mpr (h (n + j) (by omega))
  | existsRigid _ ih => exact exists_congr (fun v => ih v σ i)
  | existsFlex =>
    simp only [Formula.Holds, show (σ.suffix n).suffix i = σ.suffix (n + i) from
      funext fun j => congrArg σ (Nat.add_assoc n i j).symm]

theorem holds_disj (p q : Formula S) (σ : Behavior S) (n : Nat) :
    (p.disj q).Holds σ n ↔ p.Holds σ n ∨ q.Holds σ n := by
  classical
  simp only [Formula.disj, Formula.Holds, Classical.not_and_iff_not_or_not, Classical.not_not]

theorem holds_imp (p q : Formula S) (σ : Behavior S) (n : Nat) :
    (p.imp q).Holds σ n ↔ (p.Holds σ n → q.Holds σ n) := by
  classical
  simp only [Formula.imp, Formula.Holds, Decidable.not_and_not_right]

theorem holds_eventually (p : Formula S) (σ : Behavior S) (n : Nat) :
    p.eventually.Holds σ n ↔ ∃ j, n ≤ j ∧ p.Holds σ j := by
  classical
  simp only [Formula.eventually, Formula.Holds, Classical.not_forall, exists_prop, Classical.not_not]

theorem holds_eventuallyAngle (A : Action S) (f : StateExpr S V) (σ : Behavior S) (n : Nat) :
    (Formula.eventuallyAngle A f).Holds σ n ↔ ∃ j, n ≤ j ∧ A.angle f (σ j) (σ (j + 1)) := by
  classical
  simp only [Formula.eventuallyAngle, Formula.Holds, Action.bracket, Action.angle,
    Classical.not_forall, exists_prop, not_or, Classical.not_not]

theorem holds_leadsTo (p q : Formula S) (σ : Behavior S) (n : Nat) :
    (p.leadsTo q).Holds σ n ↔
      ∀ i, n ≤ i → p.Holds σ i → ∃ j, i ≤ j ∧ q.Holds σ j := by
  simp only [Formula.leadsTo, Formula.Holds, holds_imp, holds_eventually]

theorem holds_weakFair (A : Action S) (f : StateExpr S V) (σ : Behavior S) (n : Nat) :
    (Formula.weakFair A f).Holds σ n ↔
      ((∃ i, n ≤ i ∧ ∀ j, i ≤ j → (A.angle f).enabled (σ j)) →
        ∀ i, n ≤ i → ∃ j, i ≤ j ∧ A.angle f (σ j) (σ (j + 1))) := by
  classical
  simp only [Formula.weakFair, holds_disj, Formula.Holds, holds_eventuallyAngle, holds_eventually]
  rw [or_comm, Classical.or_iff_not_imp_left]
  simp only [Classical.not_forall, exists_prop, not_exists, Decidable.not_and_not_right]

theorem holds_strongFair (A : Action S) (f : StateExpr S V) (σ : Behavior S) (n : Nat) :
    (Formula.strongFair A f).Holds σ n ↔
      ((∀ i, n ≤ i → ∃ j, i ≤ j ∧ (A.angle f).enabled (σ j)) →
        ∀ i, n ≤ i → ∃ j, i ≤ j ∧ A.angle f (σ j) (σ (j + 1))) := by
  classical
  simp only [Formula.strongFair, holds_disj, Formula.Holds, holds_eventuallyAngle, holds_eventually]
  rw [or_comm, Classical.or_iff_not_imp_left]
  simp only [not_exists, not_and, Classical.not_forall, exists_prop, Classical.not_not]

theorem strongFair_implies_weakFair (A : Action S) (f : StateExpr S V)
    (σ : Behavior S) (n : Nat) :
    (Formula.strongFair A f).Holds σ n → (Formula.weakFair A f).Holds σ n := by
  rw [holds_strongFair, holds_weakFair]
  intro h ⟨i, _, hi⟩
  exact h fun j _ => ⟨max i j, Nat.le_max_right .., hi _ (Nat.le_max_left ..)⟩

theorem spec_invariant {init p : StatePred S} {next : Action S} {f : StateExpr S V}
    (live : Formula S) (initial : ∀ s, init s → p s)
    (preserve : ∀ s t, p s → next.bracket f s t → p t) :
    (Formula.spec init next f live).Entails (.always (.state p)) := by
  intro σ h
  change init (σ 0) ∧ (∀ j, 0 ≤ j → next.bracket f (σ j) (σ (j + 1))) ∧ live.Sat σ at h
  intro n _
  change p (σ n)
  induction n with
  | zero => exact initial _ h.1
  | succ n ih => exact preserve _ _ (ih (Nat.zero_le n)) (h.2.1 n (Nat.zero_le n))

theorem weakFair_progress {p q : StatePred S} {next A : Action S}
    {f : StateExpr S V} {g : StateExpr S W}
    (waiting : ∀ s t, p s → next.bracket f s t → p t ∨ q t)
    (progress : ∀ s t, p s → A.angle g s t → q t)
    (enabled : ∀ s, p s → (A.angle g).enabled s) :
    (Formula.conj (.alwaysBracket next f) (Formula.weakFair A g)).Entails
      ((Formula.state p).leadsTo (.state q)) := by
  intro σ h
  obtain ⟨steps, fair⟩ := h
  apply (holds_leadsTo _ _ σ 0).mpr
  intro i hi hp
  apply Classical.byContradiction
  intro hq
  have never : ∀ j, i ≤ j → ¬ q (σ j) := fun j hj hqj => hq ⟨j, hj, hqj⟩
  have persists (d : Nat) : p (σ (i + d)) := by
    induction d with
    | zero => exact hp
    | succ d ih =>
      exact (waiting _ _ ih (steps (i + d) (Nat.zero_le _))).resolve_right
        (never _ (by omega))
  have after (j : Nat) (hj : i ≤ j) : p (σ j) := by
    have he : i + (j - i) = j := by omega
    simpa only [he] using persists (j - i)
  obtain ⟨j, hj, step⟩ := (holds_weakFair A g σ 0).mp fair
    ⟨i, hi, fun k hk => enabled _ (after k hk)⟩ i hi
  exact never (j + 1) (by omega) (progress _ _ (after j hj) step)

end Silmaril.Proofs.Logic.Temporal.TLA
