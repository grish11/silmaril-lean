module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithBoundEntryEta.Replay.Script.Example.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithBoundEntryEta.Replay.Script.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithBoundEntryEta.Replay.Case.Example.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Thms

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.ScriptReplayExample

open Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.WithBoundEntryEta.ScriptReplay
open Paper.WithBoundEntryEta.ScriptReplay.Example
open Paper.WithBoundEntryEta.CaseReplay.Example (specialize)
open Paper.WithBoundEntryEta.Generators.Example (Choice)
open Paper.EntryLetObstruction.Destructure (U)

private theorem forward_run : run moves source = some target := rfl

theorem specialized_run : run moves (source.substVars specialize) = some (target.substVars specialize) := by
  rw [run_substVars, forward_run]
  rfl

theorem replay :
    Trace [Choice] [U] moves source target ∧
    Trace [U] [U] moves (source.substVars specialize) (target.substVars specialize) := by
  have ht : HasType [Choice] source [U] :=
    (Paper.Extension.Eqv.typed Paper.WithBoundEntryEta.CaseReplay.Example.pullback.1).1
  obtain ⟨q, hq, _⟩ := run_pullback ht specialize specialized_run
  have endpoint := hq.run_eq
  rw [forward_run] at endpoint
  cases Option.some.inj endpoint
  refine ⟨hq, hq.substVars ?_⟩
  intro i A hi
  cases i with
  | zero => cases Option.some.inj hi; exact .inl (.var rfl)
  | succ i => simp [At] at hi

private def firstRow : Region SequencingObstruction.Instruction →
    Option (Region SequencingObstruction.Instruction)
  | .cfg _ n rows => if h : 0 < n then some (rows ⟨0, h⟩) else none
  | _ => none

private def sameFirstRows : Region SequencingObstruction.Instruction → Prop
  | .case _ left right => firstRow left = firstRow right
  | _ => True

private theorem no_preimage :
    ¬ ∃ q, run [.caseEntry .here] q = some inverseTarget := by
  rintro ⟨q, hq⟩
  cases q with
  | cfg e n rows =>
    cases e with
    | case a left right =>
      let bs := Paper.WithBoundEntryEta.Generators.weakenRows rows
      have eq : .case a (.cfg left n bs) (.cfg right n bs) = inverseTarget := Option.some.inj hq
      have shared : sameFirstRows (.case a (.cfg left n bs) (.cfg right n bs)) := rfl
      rw [eq] at shared
      cases shared
    | _ => contradiction
  | _ => contradiction

theorem inverse_obstruction :
    HasType [U, U] inverseTarget [U] ∧
    Trace [] [U] [.caseEntry .here] closedPredecessor (inverseTarget.substVars forgetCaptures) ∧
    ¬ ∃ q, run [.caseEntry .here] q = some inverseTarget := by
  have typed : HasType [U, U] inverseTarget [U] :=
    .case (.inl (B := U) .unit)
      (.cfg (fun _ : Fin 1 => U) (.br rfl .unit) (fun _ => .br (ℓ := 1) rfl (.var (i := 2) rfl)))
      (.cfg (fun _ : Fin 1 => U) (.br rfl .unit) (fun _ => .br (ℓ := 1) rfl (.var (i := 3) rfl)))
  have before : HasType [] closedPredecessor [U] :=
    .cfg (fun _ : Fin 1 => U) (.case (.inl (B := U) .unit) (.br rfl .unit) (.br rfl .unit))
      (fun _ => .br (ℓ := 1) rfl .unit)
  have after : HasType [] (inverseTarget.substVars forgetCaptures) [U] :=
    .case (.inl (B := U) .unit)
      (.cfg (fun _ : Fin 1 => U) (.br rfl .unit) (fun _ => .br (ℓ := 1) rfl .unit))
      (.cfg (fun _ : Fin 1 => U) (.br rfl .unit) (fun _ => .br (ℓ := 1) rfl .unit))
  exact ⟨typed, .cons before rfl (.nil after), no_preimage⟩

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.ScriptReplayExample
