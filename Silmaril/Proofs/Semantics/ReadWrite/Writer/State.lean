module

public import Silmaril.Semantics.ReadWrite.Writer.State.Defs

public section
namespace Silmaril.Proofs.Semantics.ReadWrite.Writer.State

open Silmaril.Semantics.ReadWrite

universe u
variable {Address Value Memory Result : Type u} {access : Access Address Value Memory}
variable {initial final : Memory} {result : Result} {log : ValueLog Address Value}

private theorem logOp_replays {op : AccessOp Address Value Result}
    (success : LoggedState.run (access.logOp op) initial = some ((result, final), log)) :
    Trace.Replays access (FreeMonoid.toList log) initial final := by
  cases op with
  | read address =>
    change (access.read initial address).map (fun value =>
      ((value, initial), Trace.toLog [.read address value])) = _ at success
    cases read : access.read initial address with
    | none => simp [read] at success
    | some value =>
      rw [read, Option.map_some] at success
      cases success
      exact ⟨read, rfl⟩
  | write address value =>
    change (access.write initial address value).map (fun next =>
      ((PUnit.unit, next), Trace.toLog [.write address value])) = _ at success
    cases write : access.write initial address value with
    | none => simp [write] at success
    | some next =>
      rw [write, Option.map_some] at success
      cases success
      exact ⟨_, write, rfl⟩

theorem replays_of_run {program : Program Address Value Result}
    (success : LoggedState.run (program.interpret access) initial = some ((result, final), log)) :
    Trace.Replays access (FreeMonoid.toList log) initial final := by
  induction program using Cslib.FreeM.rec generalizing initial final result log with
  | pure value =>
    change some ((value, initial), 1) = _ at success
    cases success
    rfl
  | liftBind op next ih =>
    change (LoggedState.run (access.logOp op) initial).bind (fun ((reply, middle), first) =>
      (LoggedState.run (Program.interpret (next reply) access) middle).map
        fun (outcome, last) => (outcome, first * last)) = _ at success
    cases firstRun : LoggedState.run (access.logOp op) initial with
    | none => simp [firstRun] at success
    | some step =>
      obtain ⟨⟨reply, middle⟩, first⟩ := step
      simp only [firstRun, Option.bind_some] at success
      cases lastRun : LoggedState.run (Program.interpret (next reply) access) middle with
      | none => simp [lastRun] at success
      | some finish =>
        obtain ⟨⟨value, target⟩, last⟩ := finish
        simp only [lastRun, Option.map_some] at success
        cases success
        rw [FreeMonoid.toList_mul]
        exact Trace.replays_append.mpr ⟨middle, logOp_replays firstRun, ih reply lastRun⟩

end Silmaril.Proofs.Semantics.ReadWrite.Writer.State
