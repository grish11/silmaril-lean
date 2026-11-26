module

public import Silmaril.Machine.MulticoreVM.Swaps.Defs
public import Silmaril.Machine.MulticoreVM.Toy.Thms

public section

namespace Silmaril.Proofs.Machine.MulticoreVM

open Silmaril.Machine.MulticoreVM
open Silmaril.Machine.MulticoreVM.Toy
open Silmaril.Semantics.ConcurrentTrace (Word ofWord ofWord_eq_iff)

private theorem replay_of_execute {cfg final : Config}
    {source target : Schedule ThreadId (Option ThreadId)} {sourceWord targetWord : Word ThreadId Nat}
    (fromExec : execute exec source cfg = some (final, sourceWord))
    (toExec : execute exec target cfg = some (final, targetWord))
    (trace : ofWord sourceWord = ofWord targetWord) : ScheduleReplay step cfg source target := by
  intro word last run
  have executed := (execute_iff_scheduled exec source).mpr run
  have sameOutcome := Option.some.inj (executed.symm.trans fromExec)
  have sameFinal : last = final := congrArg Prod.fst sameOutcome
  have sameWord : word = sourceWord := congrArg Prod.snd sameOutcome
  subst last
  subst word
  exact ⟨targetWord, (execute_iff_scheduled exec target).mp toExec, trace⟩

theorem emit_localDiamond (cfg : Config) {a b : ThreadId} (distinct : a ≠ b)
    {x y : Nat} {p q : List Instr}
    (atA : cfg a = some ⟨x, .emit :: p⟩) (atB : cfg b = some ⟨y, .emit :: q⟩) :
    LocalDiamond step cfg ⟨a, none⟩ ⟨b, none⟩ := by
  obtain ⟨_, forward, backward, equivalent⟩ := emit_commutes cfg distinct atA atB
  have trace := (ofWord_eq_iff _ _).mpr equivalent
  exact ⟨replay_of_execute forward backward trace, replay_of_execute backward forward trace.symm⟩

end Silmaril.Proofs.Machine.MulticoreVM
