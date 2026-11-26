module

import Silmaril.Semantics.TrackA.Interaction.Guarded.Thms
import Silmaril.Semantics.TrackA.Interaction.UB.Thms
import Silmaril.Semantics.TrackA.Interaction.WeakITree.Thms

namespace Silmaril.Semantics.TrackA.Interaction.Regression

private def Poll : Signature := ⟨Unit, fun _ => Unit⟩
private def poll : Poll.Exchange := ⟨(), ()⟩
private def Count : Signature := ⟨Unit, fun _ => Nat⟩

/-- Choose a finite budget, then make that many exchanges and return. -/
private def countdown : Coalgebra Poll Count Unit (Option Nat)
  | none => .branch .delayed () some
  | some 0 => .ret ()
  | some (n + 1) => .vis () fun _ => some n

private theorem followsCountdown (n : Nat) :
    countdown.Follows (some n) (List.replicate n poll) (some 0) := by
  induction n with
  | zero => exact .nil _
  | succ n ih => exact .cons ⟨some (n + 1), .refl, .vis rfl ()⟩ ih

private theorem chooseBudget (n : Nat) : countdown.Internal none (some n) :=
  .inr ⟨.delayed, (), n, .choice (c := countdown) (x := none) (next := some) rfl n⟩

example (n : Nat) :
    Trace.finite (List.replicate n poll) (.returned ()) ∈ countdown.observes none := by
  cases n with
  | zero =>
    exact ⟨none, some 0, .nil _, .single (chooseBudget 0), rfl⟩
  | succ n =>
    exact ⟨some 0, some 0, .cons ⟨some (n + 1), .single (chooseBudget (n + 1)), .vis rfl ()⟩
      (followsCountdown n), .refl, rfl⟩

private def ExchangeStep (a b : Option Nat) : Prop := ∃ e, countdown.WeakStep a e b

private theorem exchangeDecrements {n : Nat} {y : Option Nat} (edge : ExchangeStep (some n) y) :
    ∃ m < n, y = some m := by
  obtain ⟨_, mid, silent, exchange⟩ := edge
  have eq : mid = some n := by
    rcases silent.cases_head with rfl | ⟨_, step, _⟩
    · rfl
    · rcases step with step | ⟨_, _, _, step⟩
      · cases step with
        | tau h => cases n <;> cases h
      · cases step with
        | choice h _ => cases n <;> cases h
  subst mid
  cases exchange with
  | vis h _ =>
    cases n with
    | zero => cases h
    | succ n =>
      cases h
      exact ⟨n, Nat.lt_succ_self _, rfl⟩

private theorem exchangeLands {x y : Option Nat} {e : Poll.Exchange}
    (step : countdown.Step x (.exchange e) y) : ∃ n, y = some n := by
  cases step with
  | vis layer _ =>
    cases x with
    | none => cases layer
    | some n =>
      cases n with
      | zero => cases layer
      | succ n =>
        cases layer
        exact ⟨n, rfl⟩

private theorem noInfiniteCountdown (n : Nat) : ¬ InfiniteTrace ExchangeStep (some n) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro infinite
    obtain ⟨_, step, tail⟩ := infinite.unfold
    obtain ⟨m, lt, rfl⟩ := exchangeDecrements step
    exact ih m lt tail

/-- All finite repetitions occur, but no run produces the infinite repetition. -/
example : Trace.infinite (fun _ => poll) ∉ countdown.observes none := by
  rintro ⟨path, _, follows⟩
  obtain ⟨_, _, step⟩ := follows 0
  obtain ⟨n, reached⟩ := exchangeLands step
  have afterFirst : InfiniteTrace ExchangeStep (path 1) :=
    ⟨fun n => path (n + 1), rfl, fun n => ⟨_, follows (n + 1)⟩⟩
  exact noInfiniteCountdown n (reached ▸ afterFirst)

private def NoReply : Signature := ⟨Unit, fun _ => Empty⟩
private def stuck : Coalgebra NoReply Signature.finiteChoice Unit Unit := fun _ => .vis () Empty.elim
private def deadlocked : Coalgebra NoReply Signature.finiteChoice Unit Unit :=
  fun _ => .branch .stepping Nat.zero Fin.elim0

example : Trace.finite [] (.stuck ()) ∈ stuck.observes () :=
  ⟨(), (), .nil _, .refl, ⟨⟨Empty.elim⟩, Empty.elim, rfl⟩⟩

example : Trace.finite [] (.deadlock .stepping) ∈ deadlocked.observes () :=
  ⟨(), (), .nil _, .refl, ⟨Nat.zero, ⟨Fin.elim0⟩, Fin.elim0, rfl⟩⟩

private def emptyForest : Forest Poll Signature.noChoice Unit Empty :=
  ⟨Unit, fun _ => .ret (), Empty.elim⟩

example : emptyForest.observes = ∅ := by
  ext t
  exact ⟨fun h => h.elim fun i _ => i.elim, False.elim⟩

example : UB.classify (S := Poll)
    (Trace.finite [] (.returned (some (Except.error () : Except Unit Unit)))) =
      some (Trace.finite [] (.returned (.error ()))) := rfl

example : UB.classify (S := NoReply) (A := Unit) (Trace.finite [] (.stuck ())) =
    some (Trace.finite [] (.stuck ())) := rfl

example : UB.classify (S := NoReply) (A := Unit) (Trace.finite [] (.deadlock .stepping)) =
    some (Trace.finite [] (.deadlock .stepping)) := rfl

example : UB.classify (S := Poll) (A := Unit) (Trace.finite [] .diverge) =
    some (Trace.finite [] .diverge) := rfl

example : UB.classify (S := Poll) (A := Unit) (Trace.finite [poll] (.returned none)) = none := rfl

example : (UB.bottomExtension Bool) ⊥ = ⊥ := (UB.bottomExtension Bool).map_bot

example : ¬ ∃ b : UB.Nonempty Bool, b ≤ UB.Nonempty.pure false ∧ b ≤ UB.Nonempty.pure true :=
  UB.Nonempty.no_common_lower_bound Bool.false_ne_true

example (b : UB.Nonempty Unit) : UB.Nonempty.pure () ≤ b := UB.Nonempty.pure_le_all () b

end Silmaril.Semantics.TrackA.Interaction.Regression
