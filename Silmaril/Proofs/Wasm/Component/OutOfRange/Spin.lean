module

public import Silmaril.Wasm.Component.OutOfRange.Defs
public import Silmaril.Wasm.Component.DWiringLaws.Thms
public import Silmaril.Games.Handler.Thms
public import Silmaril.Games.LTS.Thms

/-!
# The out-of-range spinner

`spinS j` answers a question `Q = (i, a)` by calling `(j, a)` forever. Its
infinite run `spinRun j Q` reads `ask Q` and then the pairs
`call (j, a)`, `answer none` (`spinMoves`). Below `widenH n` with `n ≤ j`,
every call is out of range and every answer is `none`: that run is trap
chatter (`trapChatter_spin`), so `atSizes n k (spinS j)` diverges after the
first question (`div_atSizes_spin`), while `spinS j` never diverges
(`spinS_div`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.OutOfRange

open Silmaril.Games Silmaril.Wasm.Component

variable (j : Nat) (Q : Nat × Payload)

/-- The spinner never diverges: it has no internal step. -/
theorem spinS_div : (spinS j).div = ∅ := by
  ext s
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨⟨y, -, hd⟩, -⟩
  obtain ⟨_, hst, -⟩ := hd.unfold
  cases hst with
  | tau hc => exact hc

/-- `m` rounds of calling `(j, Q.2)` and receiving `none`. -/
def spinMoves (j : Nat) (Q : Nat × Payload) : Nat → List (Move sigU sigU)
  | 0 => []
  | m + 1 => spinMoves j Q m ++ [.inl (.ask (j, Q.2)), .inl (.ans (j, Q.2) none)]

theorem spinMoves_length (m : Nat) : (spinMoves j Q m).length = 2 * m := by
  induction m with
  | zero => rfl
  | succ m ih => simp [spinMoves, ih]; omega

theorem mem_spinMoves {m : Nat} {x : Move sigU sigU} (hx : x ∈ spinMoves j Q m) :
    x = .inl (.ask (j, Q.2)) ∨ x = .inl (.ans (j, Q.2) none) := by
  induction m with
  | zero => simp [spinMoves] at hx
  | succ m ih =>
    simp only [spinMoves, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with hx | hx | hx
    · exact ih hx
    · exact .inl hx
    · exact .inr hx

theorem path_spinMoves (m : Nat) : Path (.run Q) (spinMoves j Q m) (.run Q) := by
  induction m with
  | zero => exact .nil _
  | succ m ih =>
    exact ih.append (.cons (Step.call (E := sigU) (F := sigU) Q (j, Q.2))
      (.cons (Step.reply (E := sigU) (F := sigU) Q (j, Q.2) none) (.nil _)))

/-- The states of the spinner's infinite run. -/
def spinSt (j : Nat) (Q : Nat × Payload) : Nat → (spinR j).toLTS.State
  | 0 => .idle
  | _ + 1 => .run Q PUnit.unit

/-- The traces of the spinner's infinite run. -/
def spinTr (j : Nat) (Q : Nat × Payload) : Nat → List (Move sigU sigU)
  | 0 => []
  | m + 1 => .inr (.ask Q) :: spinMoves j Q m

/-- **The infinite run of the spinner** on the question `Q`, answered `none`. -/
def spinRun (j : Nat) (Q : Nat × Payload) : (spinR j).toLTS.InfRun where
  st := spinSt j Q
  tr := spinTr j Q
  st_zero := rfl
  tr_zero := rfl
  step
    | 0 => ⟨[.inr (.ask Q)], rfl, by exact .vis (Reduction.Step.ask (R := spinR j) Q) (.nil _)⟩
    | m + 1 => ⟨[.inl (.ask (j, Q.2)), .inl (.ans (j, Q.2) none)], by simp [spinTr, spinMoves],
        .vis (Reduction.Step.call (k := fun _ => PUnit.unit) rfl)
          (.vis (Reduction.Step.resume (R := spinR j) Q (j, Q.2) (fun _ => PUnit.unit) none)
            (.nil _))⟩

theorem spinRun_unbounded : (spinRun j Q).tr.Unbounded := fun k =>
  ⟨k + 1, by show k ≤ (spinTr j Q (k + 1)).length; simp [spinTr, spinMoves_length]; omega⟩

theorem spinRun_legal (m : Nat) : Legal ((spinRun j Q).tr m) := by
  cases m with
  | zero => exact (Legal.nil : Legal (spinTr j Q 0))
  | succ m =>
    exact (⟨_, .cons (Step.ask (E := sigU) (F := sigU) Q) (path_spinMoves j Q m)⟩ :
      Legal (spinTr j Q (m + 1)))

/-- The infinite play of the spinner on `Q`. -/
theorem spin_inf : (spinRun j Q).tr.lim ∈ (spinS j).inf :=
  DStrategy.lim_mem_inf_ofLTS _ (spinRun_unbounded j Q) (spinRun_legal j Q)

/-- **The spinner's infinite play is trap chatter** below `widenH n`, `n ≤ j`. -/
theorem trapChatter_spin {n : Nat} (hj : n ≤ j) :
    TrapChatter n (spinS j) [.inr (.ask Q)] := by
  refine ⟨_, spin_inf j Q, [.inr (.ask Q)], ⟨1, List.prefix_refl _⟩,
    ⟨Q, .single (Step.ask (E := sigU) (F := sigU) Q)⟩,
    ?_, [], (Strategy.ofHandler (widenH n)).nil_mem, .right _ .nil⟩
  rintro w x ⟨m, hm⟩
  cases m with
  | zero => simpa [spinRun, spinTr] using hm.length_le
  | succ m =>
    have hx : x ∈ spinMoves j Q m := by
      have : w ++ [x] <+: spinMoves j Q m := by
        simpa [spinRun, spinTr] using hm
      exact this.subset (by simp)
    rcases mem_spinMoves j Q hx with rfl | rfl
    · exact ⟨_, rfl, hj⟩
    · exact ⟨_, rfl, rfl⟩

/-- **The spinner does not propagate traps**: it calls again after `none`. -/
theorem spin_not_trapPropagating : ¬ TrapPropagating (spinS j) := by
  intro h
  let Q : Nat × Payload := (0, default)
  have hm : [.inr (.ask Q), .inl (.ask (j, Q.2)), .inl (.ans (j, Q.2) none),
      .inl (.ask (j, Q.2))] ∈ (spinS j).toStrategy :=
    (spinS j).inf_sub (spin_inf j Q)
      ⟨3, ⟨[.inl (.ans (j, Q.2) none)], by simp [spinRun, spinTr, spinMoves]⟩⟩
  obtain ⟨g, hg⟩ := h [.inr (.ask Q), .inl (.ask (j, Q.2))] (j, Q.2) _ hm
  cases hg

/-- `narrowH k` forwards a question at once. -/
theorem narrow_mem {k : Nat} (q : (sigN k).Op) :
    [.inr (.ask q), .inl (.ask (q.1.val, q.2))] ∈ Strategy.ofHandler (narrowH k) :=
  Strategy.mem_ofHandler.2 ⟨_, .vis (Reduction.Step.ask q)
    (.vis (Reduction.Step.call (R := (narrowH k).toReduction) (q := q)
      (m := ((q.1.val, q.2) : sigU.Op)) (k := fun r => Prog.pure r) rfl) (.nil _))⟩

/-- **`atSizes n k (spinS j)` diverges after any question**, for `n ≤ j`. -/
theorem div_atSizes_spin {n k : Nat} (hj : n ≤ j) (q : (sigN k).Op) :
    [.inr (.ask q)] ∈ (DStrategy.atSizes n k (spinS j)).div := by
  rw [DStrategy.div_atSizes_iff]
  exact ⟨[.inr (.ask (q.1.val, q.2))], _, .right _ (.sync _ .nil), narrow_mem q,
    .inr (trapChatter_spin j _ hj)⟩

end Silmaril.Proofs.Wasm.Component.OutOfRange
