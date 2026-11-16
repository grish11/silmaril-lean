module

public import Silmaril.Logic.CTL.Thms
public import Mathlib.Data.Nat.Find

@[expose] public section
namespace Silmaril.Logic.CTL

theorem Until.not_of_no_target {W : Type} {R : W → W → Prop} {P Q : W → Prop}
    (hQ : ∀ w, ¬ Q w) {w : W} : ¬ Until R P Q w := by
  intro h
  induction h with
  | now hq => exact hQ _ hq
  | next _ _ _ ih => exact ih

theorem until_deadlock_iff {W : Type} (R : W → W → Prop) (P Q : W → Prop) (w : W)
    (hdead : ∀ v, ¬ R w v) : Until R P Q w ↔ Q w := by
  constructor
  · intro h
    cases h with
    | now hq => exact hq
    | next _ hr _ => exact (hdead _ hr).elim
  · exact Until.now

theorem not_globally_of_deadlock {W : Type} (R : W → W → Prop) (P : W → Prop) (w : W)
    (hdead : ∀ v, ¬ R w v) : ¬ Globally R P w := by
  rintro ⟨path, h0, hr, _⟩
  exact hdead (path 1) (h0 ▸ hr 0)

theorem Formula.ax_iff {S : Signature} (M : Model S) (p : Formula S) (w : M.toModal.World) :
    (Formula.ax p).Holds M w ↔ ∀ v, M.toModal.accessible w v → p.Holds M v := by
  classical
  simp only [Formula.ax, Formula.Holds, not_exists, not_and, not_not]

theorem Formula.ef_iff_reachable {S : Signature} (M : Model S) (p : Formula S) (w : M.toModal.World) :
    (Formula.ef p).Holds M w ↔
      ∃ v, Relation.ReflTransGen M.toModal.accessible w v ∧ p.Holds M v := by
  simpa only [Formula.ef, Formula.top, Formula.Holds, not_false_eq_true] using
    (until_true_iff_reachable M.toModal.accessible (p.Holds M) w)

theorem Formula.ag_iff_reachable {S : Signature} (M : Model S) (p : Formula S) (w : M.toModal.World) :
    (Formula.ag p).Holds M w ↔
      ∀ v, Relation.ReflTransGen M.toModal.accessible w v → p.Holds M v := by
  classical
  change (¬ (Formula.ef (.neg p)).Holds M w) ↔ _
  rw [Formula.ef_iff_reachable]
  simp only [Formula.Holds, not_exists, not_and, not_not]

theorem Formula.deadlock_iff {S : Signature} (M : Model S) (w : M.toModal.World) :
    Formula.deadlock.Holds M w ↔ ∀ v, ¬ M.toModal.accessible w v := by
  classical
  simp only [Formula.deadlock, Formula.top, Formula.Holds, not_false_eq_true,
    and_true, not_exists]

/-- Classical successor choice extends every finite prefix to an actual maximal path.
No seriality or external path-completeness premise is used. -/
theorem finite_prefix_maximal_extension {W : Type} (R : W → W → Prop)
    (n : Nat) (path : Nat → W) (hr : ∀ i, i < n → R (path i) (path (i+1))) :
    ∃ ext : Nat → W, (∀ i, i ≤ n → ext i = path i) ∧
      ((∀ i, R (ext i) (ext (i+1))) ∨
        ∃ m, n ≤ m ∧ (∀ i, i < m → R (ext i) (ext (i+1))) ∧ ∀ v, ¬ R (ext m) v) := by
  classical
  let next (x : W) : W := if h : ∃ y, R x y then Classical.choose h else x
  have next_edge (x : W) (h : ∃ y, R x y) : R x (next x) := by
    simp only [next, dite_eq_left h]
    exact Classical.choose_spec h
  let tail : Nat → W := Nat.rec (path n) (fun _ x => next x)
  let ext (i : Nat) : W := if i ≤ n then path i else tail (i-n)
  have hprefix (i : Nat) (hi : i ≤ n) : ext i = path i := ite_eq_left hi
  have suffix (i : Nat) (hi : n ≤ i) : ext i = tail (i-n) := by
    by_cases he : i = n
    · simp only [ext, he, le_refl, ite_true, Nat.sub_self, tail, Nat.rec_zero]
    · exact ite_eq_right (by omega)
  have edge_or_dead (i : Nat) : R (ext i) (ext (i+1)) ∨ ∀ v, ¬ R (ext i) v := by
    by_cases hi : i < n
    · exact Or.inl (by rw [hprefix i (by omega), hprefix (i+1) (by omega)]; exact hr i hi)
    · show R (ext i) (ext (i+1)) ∨ ∀ v, ¬ R (ext i) v
      by_cases hs : ∃ v, R (ext i) v
      · show R (ext i) (ext (i+1)) ∨ ∀ v, ¬ R (ext i) v
        left
        have he : ext (i+1) = next (ext i) := by
          rw [suffix i (by omega), suffix (i+1) (by omega)]
          have hsub : i+1-n = (i-n)+1 := by omega
          rw [hsub]
        rw [he]
        exact next_edge _ hs
      · exact Or.inr (fun v hv => hs ⟨v, hv⟩)
  refine ⟨ext, hprefix, ?_⟩
  by_cases hd : ∃ m, ∀ v, ¬ R (ext m) v
  · show (∀ i, R (ext i) (ext (i+1))) ∨ _
    right
    let m := Nat.find hd
    have terminal : ∀ v, ¬ R (ext m) v := Nat.find_spec hd
    have edges (i : Nat) (hi : i < m) : R (ext i) (ext (i+1)) :=
      (edge_or_dead i).resolve_right (Nat.find_min hd hi)
    have hn : n ≤ m := by
      by_contra hlt
      have hmn : m < n := by omega
      exact terminal (ext (m+1)) (by rw [hprefix m (by omega), hprefix (m+1) (by omega)]; exact hr m hmn)
    exact ⟨m, hn, edges, terminal⟩
  · exact Or.inl (fun i => (edge_or_dead i).resolve_right (fun hi => hd ⟨i, hi⟩))

/-- Strong AF really quantifies over both infinite and terminal finite paths. -/
theorem Formula.af_iff_all_paths {S : Signature} (M : Model S) (p : Formula S) (w : M.toModal.World) :
    (Formula.af p).Holds M w ↔ AllEventually M.toModal.accessible (p.Holds M) w := by
  classical
  constructor
  · show (Formula.af p).Holds M w → AllEventually M.toModal.accessible (p.Holds M) w
    intro h
    constructor
    · intro path h0 hr
      by_contra hnone
      exact h.1 ⟨path, h0, hr, fun n hn => hnone ⟨n, hn⟩⟩
    · intro n path h0 hr hd
      by_contra hnone
      have hnot (i : Nat) (hi : i ≤ n) : ¬ p.Holds M (path i) :=
        fun hp => hnone ⟨i, hi, hp⟩
      apply h.2
      apply (until_iff_finite_prefix _ _ _ w).mpr
      exact ⟨n, path, h0, ⟨(Formula.deadlock_iff M _).mpr hd, hnot n le_rfl⟩,
        fun i hi => ⟨hnot i (Nat.le_of_lt hi), hr i hi⟩⟩
  · show AllEventually M.toModal.accessible (p.Holds M) w → (Formula.af p).Holds M w
    intro h
    constructor
    · rintro ⟨path, h0, hr, hnot⟩
      obtain ⟨n, hp⟩ := h.1 path h0 hr
      exact hnot n hp
    · intro hu
      obtain ⟨n, path, h0, hq, hall⟩ := (until_iff_finite_prefix _ _ _ w).mp hu
      obtain ⟨i, hi, hp⟩ := h.2 n path h0 (fun i hi => (hall i hi).2)
        ((Formula.deadlock_iff M _).mp hq.1)
      rcases Nat.eq_or_lt_of_le hi with he | hlt
      · exact hq.2 (he ▸ hp)
      · exact (hall i hlt).1 hp

/-- The derived AU formula is exactly strong until on all actual maximal paths. -/
theorem Formula.au_iff_all_paths {S : Signature} (M : Model S) (p q : Formula S)
    (w : M.toModal.World) :
    (Formula.au p q).Holds M w ↔ AllUntil M.toModal.accessible (p.Holds M) (q.Holds M) w := by
  classical
  constructor
  · show (Formula.au p q).Holds M w → AllUntil M.toModal.accessible (p.Holds M) (q.Holds M) w
    intro h
    have eventual : AllEventually M.toModal.accessible (q.Holds M) w :=
      (q.af_iff_all_paths M w).mp h.2
    have guard (path : Nat → M.toModal.World) (h0 : path 0 = w) (n : Nat)
        (hr : ∀ i, i < n → M.toModal.accessible (path i) (path (i+1)))
        (hn : ∀ i, i < n → ¬ q.Holds M (path i)) :
        ∀ i, i < n → p.Holds M (path i) := by
      intro i hi
      by_contra hp
      apply h.1
      apply (until_iff_finite_prefix _ _ _ w).mpr
      exact ⟨i, path, h0, ⟨hp, hn i hi⟩,
        fun j hj => ⟨hn j (Nat.lt_trans hj hi), hr j (Nat.lt_trans hj hi)⟩⟩
    constructor
    · intro path h0 hr
      have he : ∃ n, q.Holds M (path n) := eventual.1 path h0 hr
      exact ⟨Nat.find he, Nat.find_spec he,
        guard path h0 (Nat.find he) (fun i _ => hr i) (fun _ hi => Nat.find_min he hi)⟩
    · show ∀ (n : Nat) (path : Nat → M.toModal.World), path 0 = w →
        (∀ i, i < n → M.toModal.accessible (path i) (path (i+1))) →
        (∀ v, ¬ M.toModal.accessible (path n) v) →
        ∃ j, j ≤ n ∧ q.Holds M (path j) ∧ ∀ i, i < j → p.Holds M (path i)
      intro n path h0 hr hd
      obtain ⟨j, hj, hq⟩ := eventual.2 n path h0 hr hd
      have he : ∃ k, q.Holds M (path k) := ⟨j, hq⟩
      have hk : Nat.find he ≤ n := Nat.le_trans (Nat.find_min' he hq) hj
      exact ⟨Nat.find he, hk, Nat.find_spec he,
        guard path h0 (Nat.find he) (fun i hi => hr i (Nat.lt_of_lt_of_le hi hk)) (fun _ hi => Nat.find_min he hi)⟩
  · show AllUntil M.toModal.accessible (p.Holds M) (q.Holds M) w → (Formula.au p q).Holds M w
    intro h
    have eventual : AllEventually M.toModal.accessible (q.Holds M) w := by
      constructor
      · intro path h0 hr
        obtain ⟨n, hq, _⟩ := h.1 path h0 hr
        exact ⟨n, hq⟩
      · intro n path h0 hr hd
        obtain ⟨j, hj, hq, _⟩ := h.2 n path h0 hr hd
        exact ⟨j, hj, hq⟩
    refine ⟨?_, (q.af_iff_all_paths M w).mpr eventual⟩
    intro hu
    obtain ⟨n, path, h0, hbad, hr⟩ := (until_iff_finite_prefix _ _ _ w).mp hu
    obtain ⟨ext, hprefix, maximal⟩ :=
      finite_prefix_maximal_extension M.toModal.accessible n path (fun i hi => (hr i hi).2)
    have he0 : ext 0 = w := (hprefix 0 (Nat.zero_le n)).trans h0
    have witness : ∃ k, q.Holds M (ext k) ∧ ∀ i, i < k → p.Holds M (ext i) := by
      rcases maximal with infinite | ⟨m, _, edges, terminal⟩
      · exact h.1 ext he0 infinite
      · obtain ⟨k, _, hq, hp⟩ := h.2 m ext he0 edges terminal
        exact ⟨k, hq, hp⟩
    obtain ⟨k, hq, hp⟩ := witness
    have no_target (i : Nat) (hi : i ≤ n) : ¬ q.Holds M (ext i) := by
      rw [hprefix i hi]
      rcases Nat.eq_or_lt_of_le hi with he | hlt
      · exact he ▸ hbad.2
      · exact (hr i hlt).1
    have hnk : n < k := by
      by_contra hn
      exact no_target k (by omega) hq
    exact hbad.1 (by simpa only [hprefix n le_rfl] using hp n hnk)

/-- The all-path eventuality is strong at a terminal state: the target must hold now. -/
theorem Formula.af_deadlock {S : Signature} (M : Model S) (p : Formula S) (w : M.toModal.World)
    (hdead : ∀ v, ¬ M.toModal.accessible w v) : (Formula.af p).Holds M w ↔ p.Holds M w := by
  classical
  have hd : Formula.deadlock.Holds M w := fun ⟨v, hr, _⟩ => hdead v hr
  constructor
  · intro h
    by_contra hp
    exact h.2 (.now ⟨hd, hp⟩)
  · intro hp
    refine ⟨not_globally_of_deadlock _ _ w hdead, ?_⟩
    intro hu
    exact ((until_deadlock_iff _ _ _ w hdead).mp hu).2 hp

/-- Strong universal until also requires its endpoint at a terminal state. -/
theorem Formula.au_deadlock {S : Signature} (M : Model S) (p q : Formula S) (w : M.toModal.World)
    (hdead : ∀ v, ¬ M.toModal.accessible w v) : (Formula.au p q).Holds M w ↔ q.Holds M w := by
  constructor
  · intro h
    exact (q.af_deadlock M w hdead).mp h.2
  · intro hq
    refine ⟨?_, (q.af_deadlock M w hdead).mpr hq⟩
    intro hu
    exact ((until_deadlock_iff _ _ _ w hdead).mp hu).2 hq

/-- Serial frames remove the extra terminal-delay clause from AF. -/
theorem Formula.af_serial {S : Signature} (M : Model S) (p : Formula S)
    (serial : ∀ w, ∃ v, M.toModal.accessible w v) (w : M.toModal.World) :
    (Formula.af p).Holds M w ↔ ¬ (Formula.eg (.neg p)).Holds M w := by
  have hno : ∀ v : M.toModal.World, ¬ (Formula.conj .deadlock (.neg p)).Holds M v := by
    intro v h
    obtain ⟨u, hr⟩ := serial v
    exact h.1 ⟨u, hr, fun h => h⟩
  exact ⟨fun h => h.1, fun h => ⟨h, Until.not_of_no_target hno⟩⟩

/-- The usual serial CTL dual equation for AU is recovered exactly. -/
theorem Formula.au_serial {S : Signature} (M : Model S) (p q : Formula S)
    (serial : ∀ w, ∃ v, M.toModal.accessible w v) (w : M.toModal.World) :
    (Formula.au p q).Holds M w ↔
      ¬ (Formula.eu (.neg q) (.conj (.neg p) (.neg q))).Holds M w ∧
        ¬ (Formula.eg (.neg q)).Holds M w :=
  and_congr Iff.rfl (q.af_serial M serial w)

end Silmaril.Logic.CTL
