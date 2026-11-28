module

public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Defs
public import Silmaril.SSA.SeaOfNodes.Loop.Thms
import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Thms
import Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Correctness
import Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Execution

public section

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Proofs

open Silmaril.Machine.Lir (Memory Word)
open Silmaril.Machine.RTL (Frame)
open Silmaril.Machine.RTL.SSA
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (PortTy Reg model)
open Silmaril.SSA.SeaOfNodes.Loop (appendTuple)

variable {old new : Nat} {entrySigs sigs : List (List PortTy)}
variable (mapping : InputMap old new) {g : SourceWithEntry old entrySigs sigs}
variable {targets : Checked.Phi.Targets}

private theorem header_run_fuel_iff (g : SourceWithEntry old entrySigs sigs) (input : WordTuple new)
    (initial final : Memory) (returned : List Word) (fuel : Nat) (carried : WordTuple old)
    (fr : Frame Reg) (agree : ArgsMatch fr (appendTuple carried input)) :
    run (lowerRTL (mapCaptures mapping g)) fuel ⟨⟨0, 1, 0⟩, fr, [], initial⟩ = .returned returned final ↔
      ∃ count value, g.ReturnsAfter model (mapping.pull input) count carried value ∧
        (sigs.length + 1) * (count + 1) + 1 ≤ fuel ∧ returned = [value] ∧ final = initial := by
  induction fuel using Nat.strongRecOn generalizing carried fr with
  | ind fuel ih =>
    have packet := header_activation (mapCaptures mapping g) input carried fr initial agree
    rw [step_mapCaptures mapping g model input] at packet
    cases taken : g.step model (mapping.pull input) carried with
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
          rfl
        | backedge continued _ => cases taken.symm.trans continued
    | inr next =>
      rw [taken] at packet
      obtain ⟨latched, path, reestablished⟩ := packet
      constructor
      · intro observed
        obtain ⟨remaining, spent, rest⟩ := run_after_prefix path observed
        obtain ⟨count, value, source, enough, outputs, memory⟩ :=
          (ih remaining (by omega) next latched reestablished).mp rest
        exact ⟨count + 1, value, .backedge taken source, by rw [Nat.mul_succ]; omega, outputs, memory⟩
      · rintro ⟨count, value, source, enough, outputs, memory⟩
        cases source with
        | exit returned => cases taken.symm.trans returned
        | backedge continued rest =>
          cases Sum.inr.inj (taken.symm.trans continued)
          rw [Nat.mul_succ] at enough
          let remaining := fuel - (sigs.length + 1)
          have spent : fuel = (sigs.length + 1) + remaining := by dsimp [remaining]; omega
          have ran := (ih remaining (by omega) next latched reestablished).mpr
            ⟨_, value, rest, by dsimp [remaining]; omega, outputs, memory⟩
          rw [spent, run_through_prefix path]
          exact ran

/-- Compare RTL instruction fuel to the source backedge count via the emitted schedule. -/
theorem rtl_runMain_fuel_iff (accepted : lowerChecked mapping g = some targets)
    (input : WordTuple new) (initial final : Memory) (returned : List Word) (fuel : Nat) :
    targets.1.runMain fuel 0 (words input) initial = .returned returned final ↔
      ∃ count value, g.ReturnsAfter model (mapping.pull input) count (g.initial model (mapping.pull input)) value ∧
        rtlFuel entrySigs sigs count ≤ fuel ∧ returned = [value] ∧ final = initial := by
  obtain ⟨⟨before, checked⟩, _, rfl⟩ := lowerChecked_sound accepted
  obtain ⟨started, latched, entry, agree⟩ := checked_entry_packet mapping checked input initial
  have loop := header_run_fuel_iff mapping g input initial final returned
  change (lowerRTL (mapCaptures mapping g)).runMain fuel 0 (words input) initial = .returned returned final ↔ _
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
    have bound : (sigs.length + 1) * (count + 1) + 1 ≤ remaining := by dsimp [remaining]; omega
    rw [spent, run_through_prefix entry]
    exact (loop remaining _ latched agree).mpr ⟨count, value, source, bound, outputs, memory⟩

/-- The RTL instruction budget for a native backedge bound gives the same
bounded return as the native evaluator, including the full memory frame. -/
theorem rtl_runMain_backedges_iff (accepted : lowerChecked mapping g = some targets)
    (input : WordTuple new) (initial final : Memory) (returned : List Word) (budget : Nat) :
    targets.1.runMain (rtlFuel entrySigs sigs budget) 0 (words input) initial = .returned returned final ↔
      ∃ value : Word, g.evalBackedges model budget (mapping.pull input) = some value ∧
        returned = [value] ∧ final = initial := by
  have cost (count : Nat) : rtlFuel entrySigs sigs count ≤ rtlFuel entrySigs sigs budget ↔ count ≤ budget := by
    simp only [rtlFuel, Nat.add_le_add_iff_left, Nat.add_le_add_iff_right,
      Nat.mul_le_mul_left_iff (Nat.succ_pos _)]
  rw [rtl_runMain_fuel_iff mapping accepted]
  constructor
  · rintro ⟨count, value, source, bound, outputs, memory⟩
    exact ⟨value, (g.evalBackedges_eq_some_iff model _ value budget).mpr
      ⟨count, (cost count).mp bound, source⟩, outputs, memory⟩
  · rintro ⟨value, evaluated, outputs, memory⟩
    obtain ⟨count, bound, source⟩ := (g.evalBackedges_eq_some_iff model _ value budget).mp evaluated
    exact ⟨count, value, source, (cost count).mpr bound, outputs, memory⟩

/-- The actual RTL return is the pulled native word and unchanged whole memory. -/
theorem rtl_return_iff (accepted : lowerChecked mapping g = some targets)
    (input : WordTuple new) (initial final : Memory) (returned : List Word) :
    targets.1.oracle 0 (words input) initial returned final ↔
      ∃ value : Word, value ∈ g.denote model (mapping.pull input) ∧ returned = [value] ∧ final = initial := by
  constructor
  · rintro ⟨start, started, finish, path, terminal⟩
    obtain ⟨fuel, ran⟩ := fuel_of_steps path terminal
    have observed : targets.1.runMain fuel 0 (words input) initial = .returned returned final := by
      simpa only [Prog.runMain, started] using ran
    obtain ⟨count, value, source, _, outputs, memory⟩ :=
      (rtl_runMain_fuel_iff mapping accepted input initial final returned fuel).mp observed
    exact ⟨value, (g.returns_iff_mem_denote model _ _).mp ⟨count, source⟩, outputs, memory⟩
  · rintro ⟨value, present, outputs, memory⟩
    obtain ⟨count, source⟩ := (g.returns_iff_mem_denote model _ _).mpr present
    have observed := (rtl_runMain_fuel_iff mapping accepted input initial final returned
      (rtlFuel entrySigs sigs count)).mpr ⟨count, value, source, le_rfl, outputs, memory⟩
    unfold Prog.runMain at observed
    split at observed
    · exact ⟨_, by assumption, run_returned observed⟩
    · cases observed

/-- Undefinedness is absence of any finite RTL return, independently of fuel. -/
theorem rtl_no_finite_return_iff (accepted : lowerChecked mapping g = some targets)
    (input : WordTuple new) (initial : Memory) :
    (∀ returned final, ¬ targets.1.oracle 0 (words input) initial returned final) ↔
      g.denote model (mapping.pull input) = Part.none := by
  rw [Part.eq_none_iff']
  constructor
  · intro noFinite defined
    obtain ⟨value, present⟩ := Part.dom_iff_mem.mp defined
    exact noFinite [value] initial
      ((rtl_return_iff mapping accepted input initial initial [value]).mpr ⟨value, present, rfl, rfl⟩)
  · intro absent returned final observed
    obtain ⟨value, present, _, _⟩ := (rtl_return_iff mapping accepted input initial final returned).mp observed
    exact absent (Part.dom_iff_mem.mpr ⟨value, present⟩)

/-- Native absence produces an infinite sequence of actual RTL steps. -/
theorem rtl_divOracle_iff (accepted : lowerChecked mapping g = some targets)
    (input : WordTuple new) (initial : Memory) :
    targets.1.divOracle 0 (words input) initial ↔ g.denote model (mapping.pull input) = Part.none := by
  constructor
  · rintro ⟨start, started, diverges⟩
    apply (rtl_no_finite_return_iff mapping accepted input initial).mp
    rintro returned final ⟨other, startedOther, finite⟩
    cases Option.some.inj (started.symm.trans startedOther)
    have impossible := Behaves.unique (b₁ := .diverges) (b₂ := .returned returned final) diverges finite
    cases impossible
  · intro absent
    obtain ⟨⟨before, checked⟩, _, rfl⟩ := lowerChecked_sound accepted
    obtain ⟨started, latched, entry, agree⟩ := checked_entry_packet mapping checked input initial
    let prog := lowerRTL (mapCaptures mapping g)
    let pulled := mapping.pull input
    let atHeader (s : State Reg) := ∃ (fr : Frame Reg) (carried : WordTuple old),
      s = ⟨⟨0, 1, 0⟩, fr, [], initial⟩ ∧ ArgsMatch fr (appendTuple carried input) ∧
        ∀ count value, ¬ g.ReturnsAfter model pulled count carried value
    have initialHeader : atHeader ⟨⟨0, 1, 0⟩, latched, [], initial⟩ := by
      refine ⟨latched, g.initial model pulled, rfl, agree, fun count value source => ?_⟩
      exact Part.eq_none_iff'.mp absent (Part.dom_iff_mem.mpr
        ⟨value, (g.returns_iff_mem_denote model pulled value).mp ⟨count, source⟩⟩)
    have progress (s : State Reg) (atLoop : atHeader s) :
        ∃ t, StepsNWithin prog [] (sigs.length + 1) s t ∧ atHeader t := by
      obtain ⟨fr, carried, rfl, agrees, noReturn⟩ := atLoop
      have packet := header_activation (mapCaptures mapping g) input carried fr initial agrees
      rw [step_mapCaptures mapping g model input] at packet
      cases taken : g.step model pulled carried with
      | inl value => exact (noReturn 0 value (.exit taken)).elim
      | inr next =>
        change g.step model (mapping.pull input) carried = .inr next at taken
        rw [taken] at packet
        obtain ⟨nextFrame, path, reestablished⟩ := packet
        exact ⟨_, path, nextFrame, next, rfl, reestablished,
          fun count value rest => noReturn (count + 1) value (.backedge taken rest)⟩
    let pending (s : State Reg) := ∃ n t, StepsNWithin prog [] n s t ∧ atHeader t
    refine ⟨_, started, InfiniteTrace.coinduct pending ?_ ⟨_, _, entry, initialHeader⟩⟩
    rintro s ⟨n, t, path, atLoop⟩
    cases path with
    | head first rest => exact ⟨_, first.1, _, _, rest, atLoop⟩
    | refl =>
      obtain ⟨_, next, nextHeader⟩ := progress s atLoop
      cases next with
      | head first rest => exact ⟨_, first.1, _, _, rest, nextHeader⟩

end Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Proofs
