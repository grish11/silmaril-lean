module

public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Defs
public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Thms
import Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Execution
import Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Execution
import Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Recognition
import Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Block

/-! Agreement for a guarded row preceded by a dependent arithmetic table. -/

public section

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table

open Silmaril.Machine.Lir (Memory Word)
open Silmaril.Machine.RTL (Frame)
open Silmaril.Machine.RTL.SSA
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (PortTy Reg WordOp emitOpsWithResults model registerWithResults word)
open Silmaril.SSA.SeaOfNodes.Loop (appendTuple)
open Silmaril.SSA.SeaOfNodes.Diamond (Dataflow read)
open Silmaril.SSA.RVSDG (Origin extend)
open Silmaril.SSA.SeaOfNodes.Diamond.LambdaSSA (Atom inputEnv instruction encodeTuple)
open Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA
open Silmaril.Isotope (Value)
open Silmaril.Isotope.LambdaSSA.Semantics (extend)
open Silmaril.Isotope.LambdaSSA.Semantics.Region (Eval)

variable {arity : Nat} {entrySigs : List (List PortTy)} (p : Plan arity entrySigs)

/-- Recognition reconstructs the exact typed source, including both ordered
Phi columns and the dependent preheader table. -/
theorem recognize_sound {sigs : List (List PortTy)} {g : SourceWithEntry arity entrySigs sigs}
    {p : Plan arity entrySigs} (accepted : recognize g = some p) :
    ∃ eq : p.row.sigs = sigs, eq ▸ p.graph = g :=
  Proofs.recognize_sound accepted

/-- Run the typed preheader at any producer register base following its captures. -/
theorem entry_block_at {sigs : List (List PortTy)} (offset : Nat) (flow : Dataflow WordOp (wordPorts arity) [] sigs)
    (prog : Prog Reg) (block : Block Reg) (found : prog.block? 0 0 = some block)
    (input : WordTuple arity) (mem : Memory) (ok : supported flow = true)
    (separated : arity ≤ offset)
    (ops : block.ops = emitOpsWithResults (fun p => .arg p.index) (fun i => .arg (offset + i)) flow)
    (fr : Frame Reg) (args : ArgsMatch fr input) :
    ∃ ready, StepsNWithin prog [] sigs.length ⟨⟨0, 0, 0⟩, fr, [], mem⟩
      ⟨⟨0, 0, sigs.length⟩, ready, [], mem⟩ ∧ ArgsMatch ready input ∧
      ∀ wire : Origin (wordPorts arity) (extend [] sigs) wordPort,
        ready.get (registerWithResults (fun p => .arg p.index) (fun i => .arg (offset + i)) wire) =
          some (read model wire input (flow.eval model input PUnit.unit)) :=
  Proofs.entry_block_at offset flow prog block found input mem ok separated ops fr args

/-- Run the actual scheduled RTL operations. Each typed capture and local
word read agrees with the native table, and the memory is preserved. -/
theorem entry_block {sigs : List (List PortTy)} (flow : Dataflow WordOp (wordPorts arity) [] sigs)
    (prog : Prog Reg) (block : Block Reg) (found : prog.block? 0 0 = some block)
    (input : WordTuple arity) (mem : Memory) (ok : supported flow = true)
    (ops : block.ops = emit flow) (fr : Frame Reg) (args : ArgsMatch fr input) :
    ∃ ready, StepsNWithin prog [] sigs.length ⟨⟨0, 0, 0⟩, fr, [], mem⟩
      ⟨⟨0, 0, sigs.length⟩, ready, [], mem⟩ ∧ ArgsMatch ready input ∧
      ∀ wire : Origin (wordPorts arity) (extend [] sigs) wordPort,
        ready.get (entryReg arity wire.address) =
          some (read model wire input (flow.eval model input PUnit.unit)) :=
  Proofs.entry_block flow prog block found input mem ok ops fr args

/-- Read the entry column after all producers have run, then bind the whole
bank at the entry occurrence. Both targets preserve the captured inputs. -/
theorem entry_packet (input : WordTuple arity) (fr : Frame Reg) (mem : Memory)
    (agree : ArgsMatch fr input) :
    let bank := p.graph.initial model input
    ∃ latched, StepsNWithin p.rtl [] p.entrySteps ⟨⟨0, 0, 0⟩, fr, [], mem⟩ ⟨⟨0, 1, 0⟩, latched, [], mem⟩ ∧
      ArgsMatch latched (appendTuple bank input) ∧
      Eval (instruction model) (inputEnv model input) (Generic.entry p.graph) mem 0 (encodeTuple model bank) mem :=
  Proofs.entry_packet p input fr mem agree

/-- Each actual header takes the native branch with the entire packet.
Feedback keeps the original captures and rebinds the bank simultaneously. -/
theorem header_packet (input old : WordTuple arity) (fr : Frame Reg) (mem : Memory)
    (agree : ArgsMatch fr (appendTuple old input)) :
    let eval := Eval (instruction model) (extend (inputEnv model input) (encodeTuple model old))
      (Generic.header p.graph) mem
    let after := p.row.testFrame fr old
    match p.graph.step model input old with
    | .inl value =>
      StepsNWithin p.rtl [] p.row.activationSteps ⟨⟨0, 1, 0⟩, fr, [], mem⟩
        ⟨⟨0, 2, 0⟩, after.set .phi value, [], mem⟩ ∧
      eval 1 (Generic.packResult model (out := word) value) mem
    | .inr next =>
      let latched := bindWords arity after next
      StepsNWithin p.rtl [] p.row.activationSteps ⟨⟨0, 1, 0⟩, fr, [], mem⟩
        ⟨⟨0, 1, 0⟩, latched, [], mem⟩ ∧
      ArgsMatch latched (appendTuple next input) ∧ eval 0 (encodeTuple model next) mem :=
  Preheader.Proofs.header_packet_with p.row p.flow p.entry p.preheader input old fr mem agree

section Checked

variable {sigs : List (List PortTy)} {g : SourceWithEntry arity entrySigs sigs} {targets : Checked.Phi.Targets}

/-- A successful check emits a well-formed RTL function and the native λSSA CFG. -/
theorem lowerChecked_sound (accepted : lowerChecked g = some targets) :
    ∃ p, recognize g = some p ∧ p.lowerFunc.WellFormed ∧
      targets = (p.rtl, Generic.lower g) :=
  Proofs.lowerChecked_sound accepted

/-- Successful checking certifies both emitted representations. -/
theorem lowerChecked_typed (accepted : lowerChecked g = some targets) :
    targets.1.WellFormed ∧ targets.2.HasType (Generic.inputContext (wordSorts arity))
      [Generic.packed [.value word]] :=
  Proofs.lowerChecked_typed accepted

/-- The exact machine fuel threshold includes the table and entry jump. -/
theorem rtl_runMain_fuel_iff {p : Plan arity entrySigs} (recognized : recognize g = some p)
    (accepted : lowerChecked g = some targets) (input : WordTuple arity)
    (initial final : Memory) (returned : List Word) (fuel : Nat) :
    targets.1.runMain fuel 0 (words input) initial = .returned returned final ↔
      ∃ count value, g.ReturnsAfter model input count (g.initial model input) value ∧
        p.rtlFuel count ≤ fuel ∧ returned = [value] ∧ final = initial :=
  Proofs.rtl_runMain_fuel_iff recognized accepted input initial final returned fuel

/-- The λSSA runner charges one visit per activation, with entry evaluated before the visits. -/
theorem lambda_run_succ (accepted : lowerChecked g = some targets) (input : WordTuple arity)
    (budget : Nat) :
    Generic.Fuel.run model (inputEnv model input) (budget + 1) targets.2 =
      (g.evalBackedges model budget input).map (fun value => (0, Generic.packResult model (out := word) value)) :=
  Proofs.lambda_run_succ accepted input budget

/-- Every finite machine return has the native word and the full initial memory. -/
theorem rtl_return_iff (accepted : lowerChecked g = some targets) (input : WordTuple arity)
    (initial final : Memory) (returned : List Word) :
    targets.1.oracle 0 (words input) initial returned final ↔
      ∃ value : Word, g.Returns model input value ∧ returned = [value] ∧ final = initial :=
  Proofs.rtl_return_iff accepted input initial final returned

/-- Every finite λSSA CFG return packs the native word and preserves the entire memory. -/
theorem lambda_return_iff (accepted : lowerChecked g = some targets) (input : WordTuple arity)
    (initial final : Memory) (label : Nat) (payload : Value (Atom model)) :
    Eval (instruction model) (inputEnv model input) targets.2 initial label payload final ↔
      ∃ value : Word, g.Returns model input value ∧ label = 0 ∧
        payload = Generic.packResult model (out := word) value ∧ final = initial :=
  Proofs.lambda_return_iff accepted input initial final label payload

/-- Native undefinedness is exactly absence of a finite return in either target. -/
theorem no_finite_return_iff (accepted : lowerChecked g = some targets) (input : WordTuple arity)
    (initial : Memory) :
    ((∀ returned final, ¬ targets.1.oracle 0 (words input) initial returned final) ↔
        g.denote model input = Part.none) ∧
    ((∀ label payload final, ¬ Eval (instruction model) (inputEnv model input)
        targets.2 initial label payload final) ↔ g.denote model input = Part.none) :=
  Proofs.no_finite_return_iff accepted input initial

end Checked

end Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table
