module

public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.Family.Defs
import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Thms
import Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.Family.Execution
import Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Execution

public section

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.Family.Proofs

open Silmaril.Machine.Lir (Memory Word)
open Silmaril.Machine.RTL (Frame)
open Silmaril.Machine.RTL.SSA
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (PortTy Reg model)
open Silmaril.SSA.SeaOfNodes.Loop (appendTuple)

variable {old new tests : Nat} {entrySigs sigs : List (List PortTy)}

private theorem header_run (mapping : InputMap old new) (p : Source old old entrySigs sigs tests)
    {prog : Prog Reg} (accepted : lowerChecked mapping p = some prog)
    (input : WordTuple new) (initial final : Memory) (returned : List Word) (fuel : Nat)
    (carried : WordTuple old) (fr : Frame Reg) (agree : ArgsMatch fr (appendTuple carried input)) :
    run prog fuel ⟨⟨0, 1, 0⟩, fr, [], initial⟩ = .returned returned final ↔
      ∃ slots value, p.ReturnsAlong (mapping.pull input) slots carried value ∧
        visitFuel sigs slots ≤ fuel ∧ returned = [value] ∧ final = initial := by
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
          exact ⟨[], value, .exit taken, by simp only [visitFuel]; omega, rfl, rfl⟩
      · rintro ⟨slots, result, source, enough, rfl, rfl⟩
        cases source with
        | exit returned =>
          cases Sum.inl.inj (taken.symm.trans returned)
          simp only [visitFuel] at enough
          have spent : fuel = (sigs.length + 1) + (fuel - (sigs.length + 2) + 1) := by omega
          rw [spent, run_through_prefix path, run, terminal]
        | feedback continued _ => cases taken.symm.trans continued
    | inr selected =>
      obtain ⟨slot, next⟩ := selected
      rw [taken] at packet
      obtain ⟨ready, latched, b, path, _, _, _, transfer, reestablished⟩ := packet
      have visit : StepsNWithin prog [] (sigs.length + 1 + (slot.val + 1))
          ⟨⟨0, 1, 0⟩, fr, [], initial⟩ ⟨⟨0, 1, 0⟩, latched, [], initial⟩ := by
        rw [← Nat.add_assoc]
        exact Width.Proofs.append_step path transfer
      constructor
      · intro observed
        obtain ⟨remaining, spent, rest⟩ := run_after_prefix visit observed
        obtain ⟨slots, value, source, enough, outputs, memory⟩ :=
          (ih remaining (by omega) next latched reestablished).mp rest
        exact ⟨slot :: slots, value, .feedback taken source, by simp only [visitFuel]; omega, outputs, memory⟩
      · rintro ⟨slots, value, source, enough, outputs, memory⟩
        cases source with
        | exit returned => cases taken.symm.trans returned
        | feedback continued rest =>
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Sum.inr.inj (taken.symm.trans continued))
          simp only [visitFuel] at enough
          let remaining := fuel - (sigs.length + 1 + (slot.val + 1))
          have spent : fuel = (sigs.length + 1 + (slot.val + 1)) + remaining := by dsimp [remaining]; omega
          have ran := (ih remaining (by omega) _ latched reestablished).mpr
            ⟨_, value, rest, by dsimp [remaining]; omega, outputs, memory⟩
          rw [spent, run_through_prefix visit]
          exact ran

theorem rtl_runMain_fuel_iff (mapping : InputMap old new) (p : Source old old entrySigs sigs tests)
    {prog : Prog Reg} (accepted : lowerChecked mapping p = some prog)
    (input : WordTuple new) (initial final : Memory) (returned : List Word) (fuel : Nat) :
    prog.runMain fuel 0 (words input) initial = .returned returned final ↔
      ∃ slots value, p.ReturnsAlong (mapping.pull input) slots (p.primary.initial model (mapping.pull input)) value ∧
        rtlFuel entrySigs sigs slots ≤ fuel ∧ returned = [value] ∧ final = initial := by
  obtain ⟨started, latched, entry, agree⟩ := entry_packet mapping p accepted input initial
  have loop := header_run mapping p accepted input initial final returned
  simp only [Prog.runMain, started]
  constructor
  · intro observed
    obtain ⟨remaining, spent, rest⟩ := run_after_prefix entry observed
    obtain ⟨slots, value, source, bound, outputs, memory⟩ := (loop remaining _ latched agree).mp rest
    exact ⟨slots, value, source, by unfold rtlFuel; omega, outputs, memory⟩
  · rintro ⟨slots, value, source, enough, outputs, memory⟩
    unfold rtlFuel at enough
    let remaining := fuel - (entrySigs.length + 1)
    have spent : fuel = (entrySigs.length + 1) + remaining := by dsimp [remaining]; omega
    have bound : visitFuel sigs slots ≤ remaining := by dsimp [remaining]; omega
    rw [spent, run_through_prefix entry]
    exact (loop remaining _ latched agree).mpr ⟨slots, value, source, bound, outputs, memory⟩

theorem rtl_return_iff (mapping : InputMap old new) (p : Source old old entrySigs sigs tests)
    {prog : Prog Reg} (accepted : lowerChecked mapping p = some prog)
    (input : WordTuple new) (initial final : Memory) (returned : List Word) :
    prog.oracle 0 (words input) initial returned final ↔
      ∃ slots value, p.ReturnsAlong (mapping.pull input) slots (p.primary.initial model (mapping.pull input)) value ∧
        returned = [value] ∧ final = initial := by
  constructor
  · rintro ⟨start, started, finish, path, terminal⟩
    obtain ⟨fuel, ran⟩ := fuel_of_steps path terminal
    have observed : prog.runMain fuel 0 (words input) initial = .returned returned final := by
      simpa only [Prog.runMain, started] using ran
    obtain ⟨slots, value, source, _, outputs, memory⟩ :=
      (rtl_runMain_fuel_iff mapping p accepted input initial final returned fuel).mp observed
    exact ⟨slots, value, source, outputs, memory⟩
  · rintro ⟨slots, value, source, outputs, memory⟩
    have observed := (rtl_runMain_fuel_iff mapping p accepted input initial final returned
      (rtlFuel entrySigs sigs slots)).mpr ⟨slots, value, source, le_rfl, outputs, memory⟩
    unfold Prog.runMain at observed
    split at observed
    · exact ⟨_, by assumption, run_returned observed⟩
    · cases observed

end Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.Family.Proofs
