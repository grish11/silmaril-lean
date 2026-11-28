module

public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.Defs
import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Thms
import Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.Execution
import Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Execution

public section

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.Proofs

open Silmaril.Machine.Lir (Memory Word)
open Silmaril.Machine.RTL (Frame)
open Silmaril.Machine.RTL.SSA
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (PortTy Reg model)
open Silmaril.SSA.SeaOfNodes.Loop (appendTuple)

variable {old new : Nat} {entrySigs sigs : List (List PortTy)}

private theorem header_run (mapping : InputMap old new) (p : Source old old entrySigs sigs)
    {prog : Prog Reg} (accepted : lowerChecked mapping p = some prog)
    (input : WordTuple new) (initial final : Memory) (returned : List Word) (fuel : Nat)
    (carried : WordTuple old) (fr : Frame Reg) (agree : ArgsMatch fr (appendTuple carried input)) :
    run prog fuel ⟨⟨0, 1, 0⟩, fr, [], initial⟩ = .returned returned final ↔
      ∃ count value, p.ReturnsAfter (mapping.pull input) count carried value ∧
        (sigs.length + 2) * (count + 1) ≤ fuel ∧ returned = [value] ∧ final = initial := by
  induction fuel using Nat.strongRecOn generalizing carried fr with
  | ind fuel ih =>
    have packet := checked_activation mapping p accepted input carried fr initial agree
    unfold Activation at packet
    cases taken : p.step (mapping.pull input) carried with
    | inl value =>
      rw [taken] at packet
      obtain ⟨ready, path, terminal⟩ := packet
      constructor
      · intro observed
        obtain ⟨remaining, spent, rest⟩ := run_after_prefix path observed
        cases remaining with
        | zero => cases rest
        | succ remaining =>
          rw [run, terminal] at rest
          obtain ⟨rfl, rfl⟩ := Result.returned.inj rest
          exact ⟨0, value, .exit taken, by simp only [Nat.zero_add, Nat.mul_one]; omega, rfl, rfl⟩
      · rintro ⟨count, result, source, enough, rfl, rfl⟩
        cases source with
        | exit returned =>
          cases Sum.inl.inj (taken.symm.trans returned)
          simp only [Nat.zero_add, Nat.mul_one] at enough
          have spent : fuel = (sigs.length + 1) + (fuel - (sigs.length + 2) + 1) := by omega
          rw [spent, run_through_prefix path, run, terminal]
        | feedback continued _ => cases taken.symm.trans continued
    | inr selected =>
      obtain ⟨side, next⟩ := selected
      rw [taken] at packet
      obtain ⟨ready, latched, path, _, _, _, _, transfer, reestablished⟩ := packet
      have visit := Width.Proofs.append_step path transfer
      constructor
      · intro observed
        obtain ⟨remaining, spent, rest⟩ := run_after_prefix visit observed
        obtain ⟨count, value, source, enough, outputs, memory⟩ :=
          (ih remaining (by omega) next latched reestablished).mp rest
        exact ⟨count + 1, value, .feedback taken source, by rw [Nat.mul_succ]; omega, outputs, memory⟩
      · rintro ⟨count, value, source, enough, outputs, memory⟩
        cases source with
        | exit returned => cases taken.symm.trans returned
        | feedback continued rest =>
          obtain ⟨_, rfl⟩ := Prod.mk.inj (Sum.inr.inj (taken.symm.trans continued))
          rw [Nat.mul_succ] at enough
          let remaining := fuel - (sigs.length + 2)
          have spent : fuel = (sigs.length + 2) + remaining := by dsimp [remaining]; omega
          have ran := (ih remaining (by omega) _ latched reestablished).mpr
            ⟨_, value, rest, by dsimp [remaining]; omega, outputs, memory⟩
          rw [spent, run_through_prefix visit]
          exact ran

theorem rtl_runMain_fuel_iff (mapping : InputMap old new) (p : Source old old entrySigs sigs)
    {prog : Prog Reg} (accepted : lowerChecked mapping p = some prog)
    (input : WordTuple new) (initial final : Memory) (returned : List Word) (fuel : Nat) :
    prog.runMain fuel 0 (words input) initial = .returned returned final ↔
      ∃ count value, p.ReturnsAfter (mapping.pull input) count (p.primary.initial model (mapping.pull input)) value ∧
        rtlFuel entrySigs sigs count ≤ fuel ∧ returned = [value] ∧ final = initial := by
  obtain ⟨started, latched, entry, agree⟩ := entry_packet mapping p accepted input initial
  have loop := header_run mapping p accepted input initial final returned
  simp only [Prog.runMain, started]
  constructor
  · intro observed
    obtain ⟨remaining, spent, rest⟩ := run_after_prefix entry observed
    obtain ⟨count, value, source, bound, outputs, memory⟩ := (loop remaining _ latched agree).mp rest
    exact ⟨count, value, source, by unfold rtlFuel; omega, outputs, memory⟩
  · rintro ⟨count, value, source, enough, outputs, memory⟩
    unfold rtlFuel at enough
    let remaining := fuel - (entrySigs.length + 1)
    have spent : fuel = (entrySigs.length + 1) + remaining := by dsimp [remaining]; omega
    have bound : (sigs.length + 2) * (count + 1) ≤ remaining := by dsimp [remaining]; omega
    rw [spent, run_through_prefix entry]
    exact (loop remaining _ latched agree).mpr ⟨count, value, source, bound, outputs, memory⟩

theorem rtl_return_iff (mapping : InputMap old new) (p : Source old old entrySigs sigs)
    {prog : Prog Reg} (accepted : lowerChecked mapping p = some prog)
    (input : WordTuple new) (initial final : Memory) (returned : List Word) :
    prog.oracle 0 (words input) initial returned final ↔
      ∃ count value, p.ReturnsAfter (mapping.pull input) count (p.primary.initial model (mapping.pull input)) value ∧
        returned = [value] ∧ final = initial := by
  constructor
  · rintro ⟨start, started, finish, path, terminal⟩
    obtain ⟨fuel, ran⟩ := fuel_of_steps path terminal
    have observed : prog.runMain fuel 0 (words input) initial = .returned returned final := by
      simpa only [Prog.runMain, started] using ran
    obtain ⟨count, value, source, _, outputs, memory⟩ :=
      (rtl_runMain_fuel_iff mapping p accepted input initial final returned fuel).mp observed
    exact ⟨count, value, source, outputs, memory⟩
  · rintro ⟨count, value, source, outputs, memory⟩
    have observed := (rtl_runMain_fuel_iff mapping p accepted input initial final returned
      (rtlFuel entrySigs sigs count)).mpr ⟨count, value, source, le_rfl, outputs, memory⟩
    unfold Prog.runMain at observed
    split at observed
    · exact ⟨_, by assumption, run_returned observed⟩
    · cases observed

end Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.Proofs
