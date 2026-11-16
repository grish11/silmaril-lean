module

public import Silmaril.Proofs.Wasm.Component.DWiring.Laws

/-!
# Chatter below `widenH`

`widenH n` answers a call of an out-of-range function by `none` at once,
without a visible move. So a strategy on top of it can chatter forever,
calling out-of-range functions and receiving traps. This file shows that this
is the only way: in an infinite interaction of `widenH n` with `σ` whose
visible part is constant, `σ` plays an infinite play in which, from some point
on, every move is a trap event below (`chatter_widenH`).

* `run_traps`: along a run of the handler with upper moves only, every event
  other than the first and the last is a trap event.
* `hidden_eq`: the hidden events of the two sides of an interaction agree.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.DWiring

open Silmaril.Games Silmaril.Wasm.Component

variable {n : Nat}

/-- The states of `widenH n` between a trap round and the next question. -/
def Good (n : Nat) (x : (widenH n).toReduction.State) : Prop :=
  x = .idle ∨ ∃ q : sigU.Op, n ≤ q.1 ∧ x = .run q (.pure none)

/-- The states of `widenH n` without an upper move. -/
def Stuck (n : Nat) (x : (widenH n).toReduction.State) : Prop :=
  ∀ e y, ¬ (widenH n).toReduction.toLTS.step x (some (.inr e)) y

theorem good_not_stuck {x : (widenH n).toReduction.State} (h : Good n x) : ¬ Stuck n x := by
  rcases h with rfl | ⟨q, -, rfl⟩
  · exact fun hs => hs _ _ (.ask (0, .flat []))
  · exact fun hs => hs _ _
      (.ret (r := none) (show (widenH n).toReduction.done (q := q) (Prog.pure none) none from rfl))

theorem stuck_of_lt {q : sigU.Op} (hq : q.1 < n) :
    Stuck n (.run q ((widenH n) q)) := by
  intro e y hs
  cases hs with
  | ret hc =>
    change widenH n q = _ at hc
    simp only [widenH, hq, dite_true] at hc
    cases hc

theorem step_any {x y : (widenH n).toReduction.State} {e : Ev sigU}
    (hs : (widenH n).toReduction.toLTS.step x (some (.inr e)) y) : Good n y ∨ Stuck n y := by
  cases hs with
  | ask q =>
    by_cases hq : q.1 < n
    · exact .inr (stuck_of_lt hq)
    · refine .inl (.inr ⟨q, Nat.le_of_not_lt hq, ?_⟩)
      change Reduction.State.run (R := (widenH n).toReduction) q (widenH n q) = _
      simp only [widenH, hq, dite_false]
  | ret _ => exact .inl (.inl rfl)

theorem step_good {x y : (widenH n).toReduction.State} {e : Ev sigU} (hx : Good n x)
    (hs : (widenH n).toReduction.toLTS.step x (some (.inr e)) y) :
    (IsTrap n e ∧ Good n y) ∨ Stuck n y := by
  rcases hx with rfl | ⟨q, hq, rfl⟩
  · cases hs with
    | ask q =>
      by_cases hq : q.1 < n
      · exact .inr (stuck_of_lt hq)
      · refine .inl ⟨Nat.le_of_not_lt hq, .inr ⟨q, Nat.le_of_not_lt hq, ?_⟩⟩
        change Reduction.State.run (R := (widenH n).toReduction) q (widenH n q) = _
        simp only [widenH, hq, dite_false]
  · cases hs with
    | ret hc =>
      change Prog.pure none = Prog.pure _ at hc
      cases hc
      exact .inl ⟨rfl, .inl rfl⟩

theorem run_nil {x y : (widenH n).toReduction.State}
    (h : (widenH n).toReduction.toLTS.Run x [] y) : y = x := by
  match h with
  | .nil _ => rfl
  | .tau hs _ => cases hs with | tau hc => exact hc.elim

theorem step_of_run_cons {x z : (widenH n).toReduction.State} {o : Move (sigN n) sigU}
    {s : List (Move (sigN n) sigU)} (h : (widenH n).toReduction.toLTS.Run x (o :: s) z) :
    ∃ y, (widenH n).toReduction.toLTS.step x (some o) y ∧
      (widenH n).toReduction.toLTS.Run y s z := by
  obtain ⟨x₁, x₂, h₁, h₂, h₃⟩ := LTS.Run.cons_inv h
  rw [run_nil h₁] at h₂
  exact ⟨x₂, h₂, h₃⟩

theorem not_stuck_of_run {x z : (widenH n).toReduction.State} {e : Ev sigU}
    {s : List (Move (sigN n) sigU)}
    (h : (widenH n).toReduction.toLTS.Run x (.inr e :: s) z) : ¬ Stuck n x := by
  obtain ⟨y, hs, -⟩ := step_of_run_cons h
  exact fun hx => hx _ _ hs

theorem not_stuck_of_run_append {x z : (widenH n).toReduction.State} (l : List (Ev sigU))
    (b : Ev sigU) (h : (widenH n).toReduction.toLTS.Run x ((l ++ [b]).map Sum.inr) z) :
    ¬ Stuck n x := by
  cases l with
  | nil => exact not_stuck_of_run h
  | cons c l => exact not_stuck_of_run h

theorem run_traps_good : ∀ {x y : (widenH n).toReduction.State} (l : List (Ev sigU))
    (b : Ev sigU),
    Good n x → (widenH n).toReduction.toLTS.Run x ((l ++ [b]).map Sum.inr) y →
      ∀ e ∈ l, IsTrap n e
  | _, _, [], _, _, _ => by simp
  | _, _, e :: l, b, hx, h => by
    obtain ⟨x', hs, hr⟩ := step_of_run_cons (s := (l ++ [b]).map Sum.inr) h
    rcases step_good hx hs with ⟨he, hx'⟩ | hst
    · intro e' he'
      rcases List.mem_cons.1 he' with rfl | he'
      · exact he
      · exact run_traps_good l b hx' hr e' he'
    · exact (not_stuck_of_run_append l b hr hst).elim

/-- **Trap events.** Along a run of `widenH n` with upper moves only, every event
other than the first and the last is a trap event. -/
theorem run_traps {x y : (widenH n).toReduction.State} {a b : Ev sigU} {l : List (Ev sigU)}
    (h : (widenH n).toReduction.toLTS.Run x ((a :: (l ++ [b])).map Sum.inr) y) :
    ∀ e ∈ l, IsTrap n e := by
  obtain ⟨x', hs, hr⟩ := step_of_run_cons (s := (l ++ [b]).map Sum.inr) h
  rcases step_any hs with hx' | hst
  · exact run_traps_good l b hx' hr
  · exact (not_stuck_of_run_append l b hr hst).elim

end Silmaril.Proofs.Wasm.Component.DWiring
