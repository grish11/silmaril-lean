module

public import Silmaril.Logic.Temporal.Buchi.Defs
public import Mathlib.Data.Nat.Find

@[expose] public section
namespace Silmaril.Logic.Temporal.Buchi

/-- The inner least fixed point is actual finite reachability to F ∩ EX Z. -/
theorem mem_inner_lfp {W : Type} (R : W → W → Prop) (F Z : Set W) (w : W) :
    w ∈ (inner R F Z).lfp ↔
      ∃ n, ReachIn R {x | x ∈ F ∧ ∃ v, R x v ∧ v ∈ Z} n w := by
  constructor
  · have hpre : inner R F Z {x | ∃ n, ReachIn R {y | y ∈ F ∧ ∃ v, R y v ∧ v ∈ Z} n x} ⊆
        {x | ∃ n, ReachIn R {y | y ∈ F ∧ ∃ v, R y v ∧ v ∈ Z} n x} := by
      intro x hx
      rcases hx with h | ⟨v, hr, n, hn⟩
      · exact ⟨0, h⟩
      · exact ⟨n+1, v, hr, hn⟩
    exact fun hw => (inner R F Z).lfp_le hpre hw
  · rintro ⟨n, hn⟩
    induction n generalizing w with
    | zero =>
        rw [← (inner R F Z).map_lfp]
        exact Or.inl hn
    | succ n ih =>
        obtain ⟨v, hr, hv⟩ := hn
        rw [← (inner R F Z).map_lfp]
        exact Or.inr ⟨v, hr, ih v hv⟩

/-- A ranked successor system cannot defer accepting states forever. This lemma
constructs one path, reusing its choices for every late-visit obligation. -/
theorem accepts_of_rank {W : Type} (R : W → W → Prop) (F X : Set W)
    (rank : {w // w ∈ X} → Nat)
    (next : {w // w ∈ X} → {w // w ∈ X})
    (edge : ∀ x, R x.val (next x).val)
    (decrease : ∀ x, x.val ∉ F → rank (next x) < rank x)
    (w : W) (hw : w ∈ X) : Accepts R F w := by
  let p : Nat → {w // w ∈ X} := Nat.rec ⟨w, hw⟩ (fun _ x => next x)
  have eventual : ∀ d n, rank (p n) = d → ∃ m, n ≤ m ∧ (p m).val ∈ F := by
    intro d
    induction d using Nat.strong_induction_on with
    | ind d ih =>
        intro n hn
        by_cases hf : (p n).val ∈ F
        · exact ⟨n, le_rfl, hf⟩
        · have hdec : rank (p (n+1)) < d := hn ▸ decrease (p n) hf
          obtain ⟨m, hm, hf⟩ := ih (rank (p (n+1))) hdec (n+1) rfl
          exact ⟨m, (Nat.le_succ n).trans hm, hf⟩
  exact ⟨fun n => (p n).val, rfl, fun n => edge (p n),
    fun n => eventual (rank (p n)) n rfl⟩

/-- The nested greatest/least fixed point produces one actual Büchi path on
arbitrary graphs, including infinite carriers and infinitely branching graphs. -/
theorem accepts_of_mem_gfp {W : Type} (R : W → W → Prop) (F : Set W) (w : W)
    (hw : w ∈ (outer R F).gfp) : Accepts R F w := by
  classical
  let X := (outer R F).gfp
  let T : Set W := {x | x ∈ F ∧ ∃ v, R x v ∧ v ∈ X}
  have reach (x : {x // x ∈ X}) : ∃ n, ReachIn R T n x.val := by
    apply (mem_inner_lfp R F X x.val).mp
    exact (congrArg (fun Z => x.val ∈ Z) (outer R F).map_gfp).mpr x.property
  let rank : {x // x ∈ X} → Nat := fun x => Nat.find (reach x)
  have ranked (x : {x // x ∈ X}) : ReachIn R T (rank x) x.val := Nat.find_spec (reach x)
  have toX {n : Nat} {x : W} (h : ReachIn R T n x) : x ∈ X := by
    have hl : x ∈ (inner R F X).lfp := (mem_inner_lfp R F X x).mpr ⟨n, h⟩
    exact (congrArg (fun Z => x ∈ Z) (outer R F).map_gfp).mp hl
  have successor (x : {x // x ∈ X}) :
      ∃ y : {y // y ∈ X}, R x.val y.val ∧ (x.val ∉ F → rank y < rank x) := by
    have hrank := ranked x
    cases hn : rank x with
    | zero =>
        rw [hn] at hrank
        obtain ⟨hf, v, hr, hv⟩ := hrank
        exact ⟨⟨v, hv⟩, hr, fun h => (h hf).elim⟩
    | succ n =>
        rw [hn] at hrank
        obtain ⟨v, hr, hv⟩ := hrank
        let y : {y // y ∈ X} := ⟨v, toX hv⟩
        have hle : rank y ≤ n := Nat.find_min' (reach y) hv
        exact ⟨y, hr, fun _ => Nat.lt_succ_of_le hle⟩
  choose next hnext using successor
  exact accepts_of_rank R F X rank next (fun x => (hnext x).1)
    (fun x => (hnext x).2) w hw

/-- A single accepting path witnesses the outer postfixed set. -/
theorem mem_gfp_of_accepts {W : Type} (R : W → W → Prop) (F : Set W) (w : W)
    (hw : Accepts R F w) : w ∈ (outer R F).gfp := by
  have post : {x | Accepts R F x} ⊆ outer R F {x | Accepts R F x} := by
    rintro x ⟨p, h0, edges, visits⟩
    obtain ⟨n, _, hn⟩ := visits 0
    have suffix : Accepts R F (p (n+1)) := by
      refine ⟨fun i => p (n+1+i), by simp, ?_, ?_⟩
      · intro i
        simpa [Nat.add_assoc] using edges (n+1+i)
      · intro i
        obtain ⟨m, hm, hfm⟩ := visits (n+1+i)
        refine ⟨m-(n+1), by omega, ?_⟩
        simpa [Nat.add_sub_of_le (by omega : n+1 ≤ m)] using hfm
    have build : ∀ k j, p (j+k) ∈ F → Accepts R F (p (j+k+1)) →
        ReachIn R {y | y ∈ F ∧ ∃ v, R y v ∧ Accepts R F v} k (p j) := by
      intro k
      induction k with
      | zero =>
          intro j hf hs
          exact ⟨hf, p (j+1), edges j, hs⟩
      | succ k ih =>
          intro j hf hs
          exact ⟨p (j+1), edges j, ih (j+1)
            (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hf)
            (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hs)⟩
    apply (mem_inner_lfp R F {y | Accepts R F y} x).mpr
    exact ⟨n, by simpa [h0] using build n 0 (by simpa using hn) (by simpa using suffix)⟩
  exact (outer R F).le_gfp post hw


/-- Büchi acceptance is exactly the genuine nested νμ set semantics. -/
theorem accepts_iff_gfp {W : Type} (R : W → W → Prop) (F : Set W) (w : W) :
    Accepts R F w ↔ w ∈ (outer R F).gfp :=
  ⟨mem_gfp_of_accepts R F w, accepts_of_mem_gfp R F w⟩

end Silmaril.Logic.Temporal.Buchi
