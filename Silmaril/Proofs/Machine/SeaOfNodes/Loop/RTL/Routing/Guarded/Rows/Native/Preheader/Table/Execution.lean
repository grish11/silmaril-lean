module

public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Defs
public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Thms
import Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.Column
import Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.Execution
import Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Execution
import Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Block
import Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Recognition

public section

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Proofs

open Silmaril.Machine.Lir (Memory Word)
open Silmaril.Machine.RTL (Frame)
open Silmaril.Machine.RTL.SSA
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (PortTy Reg model word)
open Silmaril.SSA.SeaOfNodes.Loop (appendTuple)
open Silmaril.SSA.SeaOfNodes.Diamond.LambdaSSA (Atom inputEnv instruction encodeTuple)
open Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA
open Silmaril.Isotope (Value)
open Silmaril.Isotope.LambdaSSA.Semantics (extend)
open Silmaril.Isotope.LambdaSSA.Semantics.Region (Eval)

variable {arity : Nat} {entrySigs : List (List PortTy)} (p : Plan arity entrySigs)

theorem entry_packet (input : WordTuple arity) (fr : Frame Reg) (mem : Memory)
    (agree : ArgsMatch fr input) :
    let bank := p.graph.initial model input
    ∃ latched, StepsNWithin p.rtl [] p.entrySteps ⟨⟨0, 0, 0⟩, fr, [], mem⟩ ⟨⟨0, 1, 0⟩, latched, [], mem⟩ ∧
      ArgsMatch latched (appendTuple bank input) ∧
      Eval (instruction model) (inputEnv model input) (Generic.entry p.graph) mem 0 (encodeTuple model bank) mem := by
  let bank := p.graph.initial model input
  have block : p.rtl.block? 0 0 = some p.preheader := rfl
  obtain ⟨ready, steps, captures, readWire⟩ :=
    entry_block p.flow p.rtl p.preheader block input mem p.arithmetic rfl fr agree
  have reads : ready.readAll (p.entry.addresses.map (entryReg arity)) = some (words bank) :=
    Routing.Proofs.readColumnWith_eq (entryReg arity) p.entry input _ ready readWire
  have fetchJump : p.rtl.fetch ⟨0, 0, entrySigs.length⟩ = some (.term p.preheader.term) := by
    rw [← emit_length p.flow]
    exact Prog.fetch_term block
  have jump : step p.rtl ⟨⟨0, 0, entrySigs.length⟩, ready, [], mem⟩ =
      .running ⟨⟨0, 1, 0⟩, bindWords arity ready bank, [], mem⟩ := by
    simp only [step, fetchJump, Plan.preheader]
    exact Routing.Proofs.transfer_bank_from p.row.graph p.preheader _ _ _ rfl reads
  have appendJump {n : Nat} {start middle finish : State Reg}
      (path : StepsNWithin p.rtl [] n start middle) (last : step p.rtl middle = .running finish)
      (stack : List.IsSuffix [] finish.stack) :
      StepsNWithin p.rtl [] (n + 1) start finish := by
    induction path with
    | refl => exact .head ⟨last, stack⟩ .refl
    | head next _ ih => exact .head next (ih last)
  exact ⟨_, appendJump steps jump List.nil_suffix, bank_matches_at captures bank,
    Generic.entry_eval p.graph model input mem⟩

theorem runMain_fuel_iff (input : WordTuple arity) (initial final : Memory)
    (returned : List Word) (fuel : Nat) :
    p.rtl.runMain fuel 0 (words input) initial = .returned returned final ↔
      ∃ count value, p.graph.ReturnsAfter model input count (p.graph.initial model input) value ∧
        p.rtlFuel count ≤ fuel ∧ returned = [value] ∧ final = initial := by
  obtain ⟨latched, path, args, _⟩ := entry_packet p input _ initial (bindWords_args input)
  have run := Preheader.Proofs.runMain_fuel_iff_with p.row p.flow p.entry p.preheader p.entrySteps
    input initial final returned fuel rfl ⟨latched, path, args⟩
  exact run.trans (exists_congr fun count => exists_congr fun _ =>
    and_congr_right fun _ => and_congr (by unfold Plan.entrySteps Plan.rtlFuel Rows.Plan.rtlFuel; omega) Iff.rfl)

section Checked

variable {sigs : List (List PortTy)} {g : SourceWithEntry arity entrySigs sigs} {targets : Checked.Phi.Targets}

theorem lowerChecked_sound (accepted : lowerChecked g = some targets) :
    ∃ p, recognize g = some p ∧ p.lowerFunc.WellFormed ∧
      targets = (p.rtl, Generic.lower g) := by
  unfold lowerChecked at accepted
  cases found : recognize g with
  | none => simp [found] at accepted
  | some p =>
    simp only [found, Option.bind_some] at accepted
    split at accepted
    · exact ⟨p, rfl, by assumption, (Option.some.inj accepted).symm⟩
    · cases accepted

theorem lowerChecked_typed (accepted : lowerChecked g = some targets) :
    targets.1.WellFormed ∧ targets.2.HasType (Generic.inputContext (wordSorts arity))
      [Generic.packed [.value word]] := by
  obtain ⟨p, _, wellFormed, rfl⟩ := lowerChecked_sound accepted
  exact ⟨by simpa [Plan.rtl, Plan.lowerFunc, lowerBankFrom, Prog.WellFormed] using wellFormed, Generic.lower_hasType g⟩

theorem rtl_runMain_fuel_iff {p : Plan arity entrySigs} (recognized : recognize g = some p)
    (accepted : lowerChecked g = some targets) (input : WordTuple arity)
    (initial final : Memory) (returned : List Word) (fuel : Nat) :
    targets.1.runMain fuel 0 (words input) initial = .returned returned final ↔
      ∃ count value, g.ReturnsAfter model input count (g.initial model input) value ∧
        p.rtlFuel count ≤ fuel ∧ returned = [value] ∧ final = initial := by
  obtain ⟨q, found, _, rfl⟩ := lowerChecked_sound accepted
  cases Option.some.inj (found.symm.trans recognized)
  obtain ⟨rfl, rfl⟩ := recognize_sound found
  exact runMain_fuel_iff p input initial final returned fuel

theorem lambda_run_succ (accepted : lowerChecked g = some targets) (input : WordTuple arity)
    (budget : Nat) :
    Generic.Fuel.run model (inputEnv model input) (budget + 1) targets.2 =
      (g.evalBackedges model budget input).map (fun value => (0, Generic.packResult model (out := word) value)) := by
  obtain ⟨_, _, _, rfl⟩ := lowerChecked_sound accepted
  exact Generic.Fuel.run_succ g model input budget

theorem rtl_return_iff (accepted : lowerChecked g = some targets) (input : WordTuple arity)
    (initial final : Memory) (returned : List Word) :
    targets.1.oracle 0 (words input) initial returned final ↔
      ∃ value : Word, g.Returns model input value ∧ returned = [value] ∧ final = initial := by
  obtain ⟨p, recognized, _, rfl⟩ := lowerChecked_sound accepted
  obtain ⟨rfl, rfl⟩ := recognize_sound recognized
  exact Preheader.Proofs.rtl_returns_of_fuel p.graph p.rtl p.rtlFuel input initial final returned
    (runMain_fuel_iff p input initial final returned)

theorem lambda_return_iff (accepted : lowerChecked g = some targets) (input : WordTuple arity)
    (initial final : Memory) (label : Nat) (payload : Value (Atom model)) :
    Eval (instruction model) (inputEnv model input) targets.2 initial label payload final ↔
      ∃ value : Word, g.Returns model input value ∧ label = 0 ∧
        payload = Generic.packResult model (out := word) value ∧ final = initial := by
  obtain ⟨_, _, _, rfl⟩ := lowerChecked_sound accepted
  exact Generic.lower_eval_iff g model input initial final label payload

end Checked


theorem no_finite_return_iff {sigs : List (List PortTy)} {g : SourceWithEntry arity entrySigs sigs}
    {targets : Checked.Phi.Targets} (accepted : lowerChecked g = some targets)
    (input : WordTuple arity) (initial : Memory) :
    ((∀ returned final, ¬ targets.1.oracle 0 (words input) initial returned final) ↔
        g.denote model input = Part.none) ∧
    ((∀ label payload final, ¬ Eval (instruction model) (inputEnv model input)
        targets.2 initial label payload final) ↔ g.denote model input = Part.none) :=
  Preheader.Proofs.no_finite_return_iff_of_returns g targets input initial
    (rtl_return_iff accepted input initial) (lambda_return_iff accepted input initial)

end Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Proofs
