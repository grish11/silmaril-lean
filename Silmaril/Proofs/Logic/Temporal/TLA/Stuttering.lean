module

public import Silmaril.Logic.Temporal.TLA.Defs

public section

namespace Silmaril.Proofs.Logic.Temporal.TLA

open Silmaril.Logic.Temporal.TLA

universe u v w

variable {S : Type u} {V : Type v}

private def identity : Retiming :=
  ⟨id, rfl, fun _ => Or.inr rfl, fun j => ⟨j, Nat.le_refl j⟩⟩

private theorem index_mono (r : Retiming) {i j : Nat} (h : i ≤ j) :
    r.index i ≤ r.index j := by
  induction h with
  | refl => exact Nat.le_refl _
  | @step j _ ih =>
    change r.index i ≤ r.index (j + 1)
    rcases r.step j with h | h <;> omega

private def compose (r t : Retiming) : Retiming where
  index i := r.index (t.index i)
  zero := (congrArg r.index t.zero).trans r.zero
  step i := by
    rcases t.step i with h | h
    · exact Or.inl (congrArg r.index h)
    · simpa only [h] using r.step (t.index i)
  cofinal j := by
    obtain ⟨k, hk⟩ := r.cofinal j
    obtain ⟨i, hi⟩ := t.cofinal k
    exact ⟨i, Nat.le_trans hk (index_mono r hi)⟩

/-- Every original edge at or after the current index is eventually crossed. -/
theorem retiming_crosses (r : Retiming) {i j : Nat} (h : r.index i ≤ j) :
    ∃ k, i ≤ k ∧ r.index k = j ∧ r.index (k + 1) = j + 1 := by
  obtain ⟨m, hm⟩ := r.cofinal (j + 1)
  induction m with
  | zero => rw [r.zero] at hm; omega
  | succ m ih =>
    by_cases earlier : j + 1 ≤ r.index m
    · exact ih earlier
    have later : i ≤ m := by
      apply Classical.byContradiction
      intro hn
      have := index_mono r (show m + 1 ≤ i by omega)
      omega
    rcases r.step m with he | he
    · omega
    · exact ⟨m, later, by omega, by omega⟩

/-- Advance the clocks across a repetition on either side, or cross the next
shared edge together. Each iteration advances at least one clock. -/
private def advance (r t : Retiming) (p : Nat × Nat) : Nat × Nat :=
  if r.index (p.1 + 1) = r.index p.1 then (p.1 + 1, p.2)
  else if t.index (p.2 + 1) = t.index p.2 then (p.1, p.2 + 1)
  else (p.1 + 1, p.2 + 1)

private def align (r t : Retiming) : Nat → Nat × Nat
  | 0 => (0, 0)
  | n + 1 => advance r t (align r t n)

private theorem align_step (r t : Retiming) (n : Nat) :
    let p := align r t n
    let q := align r t (n + 1)
    (q.1 = p.1 ∨ q.1 = p.1 + 1) ∧ (q.2 = p.2 ∨ q.2 = p.2 + 1) ∧
      p.1 + p.2 < q.1 + q.2 := by
  simp only [align, advance]
  split
  · exact ⟨Or.inr rfl, Or.inl rfl, by omega⟩
  · split
    · exact ⟨Or.inl rfl, Or.inr rfl, by omega⟩
    · exact ⟨Or.inr rfl, Or.inr rfl, by omega⟩

private theorem align_agrees (r t : Retiming) (n : Nat) :
    r.index (align r t n).1 = t.index (align r t n).2 := by
  induction n with
  | zero => exact r.zero.trans t.zero.symm
  | succ n ih =>
    simp only [align, advance]
    split
    · rename_i hr
      exact hr.trans ih
    · rename_i hr
      split
      · rename_i ht
        exact ih.trans ht.symm
      · rename_i ht
        rw [(r.step _).resolve_left hr, (t.step _).resolve_left ht, ih]

private theorem align_bound (r t : Retiming) (n : Nat) :
    n ≤ (align r t n).1 + (align r t n).2 := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih => have := (align_step r t n).2.2; omega

private theorem synchronize (r t : Retiming) :
    ∃ a b : Retiming, ∀ n, r.index (a.index n) = t.index (b.index n) := by
  have left (i : Nat) : ∃ n, i ≤ (align r t n).1 := by
    obtain ⟨j, hj⟩ := t.cofinal (r.index i + 1)
    refine ⟨i + j, ?_⟩
    apply Classical.byContradiction
    intro hi
    have bound := align_bound r t (i + j)
    have hr := index_mono r (show (align r t (i + j)).1 ≤ i by omega)
    have ht := index_mono t (show j ≤ (align r t (i + j)).2 by omega)
    have eq := align_agrees r t (i + j)
    omega
  have right (j : Nat) : ∃ n, j ≤ (align r t n).2 := by
    obtain ⟨i, hi⟩ := r.cofinal (t.index j + 1)
    refine ⟨i + j, ?_⟩
    apply Classical.byContradiction
    intro hj
    have bound := align_bound r t (i + j)
    have hr := index_mono r (show i ≤ (align r t (i + j)).1 by omega)
    have ht := index_mono t (show (align r t (i + j)).2 ≤ j by omega)
    have eq := align_agrees r t (i + j)
    omega
  exact ⟨⟨fun n => (align r t n).1, rfl, fun n => (align_step r t n).1, left⟩,
    ⟨fun n => (align r t n).2, rfl, fun n => (align_step r t n).2.1, right⟩,
    align_agrees r t⟩

theorem stutter_refl (σ : Behavior S) : StutterEquiv σ σ :=
  ⟨identity, identity, rfl⟩

theorem stutter_retime (σ : Behavior S) (r : Retiming) : StutterEquiv σ (σ.retime r) :=
  ⟨r, identity, rfl⟩

theorem stutter_symm {σ τ : Behavior S} (h : StutterEquiv σ τ) : StutterEquiv τ σ :=
  let ⟨r, t, h⟩ := h
  ⟨t, r, h.symm⟩

theorem stutter_trans {σ τ ρ : Behavior S}
    (h : StutterEquiv σ τ) (h' : StutterEquiv τ ρ) : StutterEquiv σ ρ := by
  obtain ⟨r, t, h⟩ := h
  obtain ⟨u, v, h'⟩ := h'
  obtain ⟨a, b, aligned⟩ := synchronize t u
  refine ⟨compose r a, compose v b, funext fun n => ?_⟩
  exact (congrFun h (a.index n)).trans
    ((congrArg τ (aligned n)).trans (congrFun h' (b.index n)))

theorem stutter_map (f : S → V) {σ τ : Behavior S} (h : StutterEquiv σ τ) :
    StutterEquiv (σ.map f) (τ.map f) :=
  let ⟨r, t, h⟩ := h
  ⟨r, t, congrArg (Behavior.map f) h⟩

/-- A suffix of an expansion expands the corresponding original suffix. -/
theorem stutter_suffix_retime (σ : Behavior S) (r : Retiming) (i : Nat) :
    StutterEquiv ((σ.retime r).suffix i) (σ.suffix (r.index i)) := by
  let tail : Retiming := {
    index := fun j => r.index (i + j) - r.index i
    zero := by simp
    step := fun j => by
      have bound := index_mono r (Nat.le_add_right i j)
      rcases r.step (i + j) with same | next
      · left
        rw [← Nat.add_assoc, same]
      · right
        rw [← Nat.add_assoc, next]
        omega
    cofinal := fun j => by
      obtain ⟨k, hk⟩ := r.cofinal (r.index i + j)
      have bound := index_mono r (Nat.le_add_left k i)
      exact ⟨k, by omega⟩ }
  have same : (σ.suffix (r.index i)).retime tail = (σ.retime r).suffix i := by
    funext j
    have bound := index_mono r (Nat.le_add_right i j)
    simp only [Behavior.retime, Behavior.suffix, tail]
    rw [show r.index i + (r.index (i + j) - r.index i) = r.index (i + j) by omega]
  rw [← same]
  exact stutter_symm (stutter_retime _ tail)

theorem hide_stutterInvariant (p : Behavior (S × V) → Prop) : StutterInvariant (hide p) := by
  intro σ τ h
  constructor
  · rintro ⟨ρ, he, hp⟩
    exact ⟨ρ, stutter_trans (stutter_symm h) he, hp⟩
  · rintro ⟨ρ, he, hp⟩
    exact ⟨ρ, stutter_trans h he, hp⟩

theorem holds_retime (p : Formula S) (σ : Behavior S) (r : Retiming) (i : Nat) :
    p.Holds (σ.retime r) i ↔ p.Holds σ (r.index i) := by
  induction p generalizing i with
  | state => rfl
  | alwaysBracket A f =>
    constructor
    · intro h j hj
      obtain ⟨k, hik, hk, hk'⟩ := retiming_crosses r hj
      simpa only [Behavior.retime, hk, hk'] using h k hik
    · intro h j hj
      change A.bracket f (σ (r.index j)) (σ (r.index (j + 1)))
      rcases r.step j with same | next
      · exact Or.inr (congrArg (f ∘ σ) same)
      · rw [next]
        exact h (r.index j) (index_mono r hj)
  | neg _ ih => exact not_congr (ih σ i)
  | conj _ _ ihp ihq => exact and_congr (ihp σ i) (ihq σ i)
  | always p ih =>
    constructor
    · intro h j hj
      obtain ⟨k, hik, hk, _⟩ := retiming_crosses r hj
      simpa only [hk] using (ih σ k).mp (h k hik)
    · intro h j hj
      exact (ih σ j).mpr (h (r.index j) (index_mono r hj))
  | existsRigid _ ih => exact exists_congr (fun v => ih v σ i)
  | existsFlex => exact hide_stutterInvariant _ (stutter_suffix_retime σ r i)

private theorem sat_retime (p : Formula S) (σ : Behavior S) (r : Retiming) :
    p.Sat (σ.retime r) ↔ p.Sat σ := by
  simpa only [Formula.Sat, r.zero] using holds_retime p σ r 0

theorem sat_stutterInvariant (p : Formula S) : StutterInvariant p.Sat := by
  intro σ τ ⟨r, t, h⟩
  exact (sat_retime p σ r).symm.trans (h ▸ sat_retime p τ t)

theorem hide_map_iff {T : Type w} (f : T → S) {p : Behavior (S × V) → Prop}
    (hp : StutterInvariant p) (σ : Behavior T) :
    hide (fun τ => p (τ.map fun z => (f z.1, z.2))) σ ↔ hide p (σ.map f) := by
  constructor
  · rintro ⟨τ, hσ, hτ⟩
    refine ⟨τ.map (fun z => (f z.1, z.2)), ?_, hτ⟩
    exact stutter_map f hσ
  · rintro ⟨τ, ⟨r, t, agrees⟩, hτ⟩
    let lifted : Behavior (T × V) := fun i => (σ.retime r i, (τ.retime t i).2)
    have projection : lifted.map Prod.fst = σ.retime r := rfl
    have mapped : lifted.map (fun z => (f z.1, z.2)) = τ.retime t :=
      funext fun i => Prod.ext (congrFun agrees i) rfl
    refine ⟨lifted, ?_, ?_⟩
    · rw [projection]
      exact stutter_retime σ r
    · change p (lifted.map _)
      rw [mapped]
      exact (hp (stutter_retime τ t)).mp hτ

/-- Lamport's full-state, two-witness clause for hiding on product states. -/
theorem hide_iff_lamport {p : Behavior (S × V) → Prop} (hp : StutterInvariant p)
    (σ : Behavior (S × V)) :
    hide p (σ.map Prod.fst) ↔
      ∃ ρ τ : Behavior (S × V), StutterEquiv σ ρ ∧ ρ.map Prod.fst = τ.map Prod.fst ∧ p τ := by
  constructor
  · rintro ⟨τ, ⟨r, t, h⟩, hτ⟩
    exact ⟨σ.retime r, τ.retime t, stutter_retime σ r, h, (hp (stutter_retime τ t)).mp hτ⟩
  · rintro ⟨ρ, τ, hσ, he, hτ⟩
    exact ⟨τ, he ▸ stutter_map Prod.fst hσ, hτ⟩

end Silmaril.Proofs.Logic.Temporal.TLA
