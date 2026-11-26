module

public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Defs
public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Reindex.Thms
public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Thms
import Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Correctness
import Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.WellFormed
import Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Execution

/-! Source transport and the checked emissions at a different capture width. -/

public section

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width

open Silmaril.Machine.Lir (Memory Word)
open Silmaril.Machine.RTL (Frame)
open Silmaril.Machine.RTL.SSA (State StepsNWithin step)
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (PortTy Reg WordOp model word)
open Silmaril.SSA.SeaOfNodes.Loop (appendTuple)
open Silmaril.SSA.RVSDG (Origin Port Tuple extend)
open Silmaril.SSA.SeaOfNodes.Diamond (Model Val read)
open Silmaril.SSA.SeaOfNodes.Diamond.LambdaSSA (Atom inputEnv instruction)
open Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA
open Silmaril.Isotope (Value)
open Silmaril.Isotope.LambdaSSA.Semantics (Diverges)
open Silmaril.Isotope.LambdaSSA.Semantics.Region (Eval)

universe w

variable {old new bank : Nat} {entrySigs sigs rightEntry rightSigs : List (List PortTy)}
variable (mapping : InputMap old new) (g : Source old bank entrySigs sigs)
variable (m : Model.{0, 0, w} WordOp) (input : Tuple (Val m.value) (wordPorts new))

/-- Changing the capture width keeps the same typed position in the bank. -/
theorem headerPort_bank {t : PortTy} (p : Port (wordPorts bank) t) :
    headerPort mapping (suffixPort (wordPorts old) p) = suffixPort (wordPorts new) p :=
  Proofs.headerPort_bank mapping p

/-- The dependent producer table and entry latch commute with the pullback. -/
theorem initial_mapCaptures :
    (mapCaptures mapping g).initial m input = g.initial m (mapping.pull input) :=
  Proofs.initial_mapCaptures mapping g m input

/-- Each activation reads the pulled captures and the same old carried bank. -/
theorem step_mapCaptures (carried : Tuple (Val m.value) (wordPorts bank)) :
    (mapCaptures mapping g).step m input carried = g.step m (mapping.pull input) carried :=
  Proofs.step_mapCaptures mapping g m input carried

/-- The mapped source has the same native partial result at the pulled valuation. -/
theorem denote_mapCaptures :
    (mapCaptures mapping g).denote m input = g.denote m (mapping.pull input) :=
  Proofs.denote_mapCaptures mapping g m input

/-- The all-input equation for the mapped graphs tests the image of the pullback. -/
theorem equation_on_image (right : Source old bank rightEntry rightSigs) :
    (∀ input : WordTuple new,
      (mapCaptures mapping g).denote model input = (mapCaptures mapping right).denote model input) ↔
    ∀ oldInput ∈ Set.range (fun input : WordTuple new => mapping.pull input),
      g.denote model oldInput = right.denote model oldInput :=
  Proofs.equation_on_image mapping g right

/-- The actual emitted λSSA header keeps taking backedges from a bank with no finite return. -/
theorem lower_diverges_of_absent (g : Source new bank entrySigs sigs)
    (input : WordTuple new) (initial : Memory) (absent : g.denote model input = Part.none) :
    Diverges (instruction model) (.region (inputEnv model input) (Generic.lower g) initial) :=
  Proofs.lower_diverges_of_absent g input initial absent

/-- Capture parameters, carried parameters and the two producer namespaces
are disjoint at arbitrary widths. -/
theorem layout_disjoint (captures bank : Nat) :
    List.Disjoint (paramRegs 0 captures) (paramRegs captures bank) ∧
    (∀ i, resultReg captures bank i ∉ paramRegs 0 captures ++ paramRegs captures bank) ∧
    (∀ i, Reg.node i ∉ paramRegs 0 captures ++ paramRegs captures bank ∧
      ∀ j, Reg.node i ≠ resultReg captures bank j) :=
  Proofs.layout_disjoint captures bank

/-- The ordinary RTL checker accepts the emitted function. Typed origins give
dominated uses and both incoming columns match the header parameters. -/
theorem lowerFunc_wellFormed {captures : Nat} (source : Source captures bank entrySigs sigs) :
    (lowerFunc source).WellFormed :=
  Proofs.lowerFunc_wellFormed source

/-- Resize and re-emit after a single successful ordinary source admission. -/
theorem lowerChecked_of_accepted (mapping : InputMap old new)
    {g : SourceWithEntry old entrySigs sigs} {before : Checked.Phi.Targets}
    (accepted : Table.lowerChecked g = some before) :
    lowerChecked mapping g =
      some (lowerRTL (mapCaptures mapping g), Generic.lower (mapCaptures mapping g)) :=
  Proofs.lowerChecked_of_accepted mapping accepted

/-- The ordinary checked source supplies the arithmetic admission for the resized entry. -/
theorem checked_entry_packet {old new : Nat} (mapping : InputMap old new)
    {g : SourceWithEntry old entrySigs sigs} {before : Checked.Phi.Targets}
    (accepted : Table.lowerChecked g = some before) (input : WordTuple new) (mem : Memory) :
    let program := lowerRTL (mapCaptures mapping g)
    let start : State Reg := ⟨⟨0, 0, 0⟩, bindWords 0 Frame.empty input, [], mem⟩
    program.start 0 (words input) mem = some start ∧
      ∃ latched, StepsNWithin program [] (entrySigs.length + 1) start
        ⟨⟨0, 1, 0⟩, latched, [], mem⟩ ∧
        ArgsMatch latched (appendTuple (g.initial model (mapping.pull input)) input) :=
  Proofs.checked_entry_packet mapping accepted input mem

/-- If the header's emitted producer registers match the native reads, its actual
conditional exits with the selected word or simultaneously transfers the old-frame
feedback column. Both paths preserve the entire memory. -/
theorem header_terminator {captures : Nat} (g : Source captures bank entrySigs sigs) (input : WordTuple captures)
    (old : WordTuple bank) (fr : Frame Reg) (mem : Memory) (capturesMatch : ArgsMatch fr input)
    (guard : fr.get (register g.predicate.address) = some
      (if (read model g.predicate (appendTuple old input)
        (g.header.eval model (appendTuple old input) PUnit.unit)).down then 1 else 0))
    (wordsMatch : ∀ wire : Origin (wordPorts captures ++ wordPorts bank) (extend [] sigs) wordPort,
      fr.get (register wire.address) = some
        (read model wire (appendTuple old input) (g.header.eval model (appendTuple old input) PUnit.unit))) :
    match g.step model input old with
    | .inl value =>
      step (lowerRTL g) ⟨⟨0, 1, sigs.length⟩, fr, [], mem⟩ =
        .running ⟨⟨0, 2, 0⟩, fr.set .phi value, [], mem⟩ ∧
      step (lowerRTL g) ⟨⟨0, 2, 0⟩, fr.set .phi value, [], mem⟩ = .returned [value] mem
    | .inr next =>
      step (lowerRTL g) ⟨⟨0, 1, sigs.length⟩, fr, [], mem⟩ =
        .running ⟨⟨0, 1, 0⟩, bindWords captures fr next, [], mem⟩ ∧
      ArgsMatch (bindWords captures fr next) (appendTuple next input) :=
  Proofs.header_terminator g input old fr mem capturesMatch guard wordsMatch

variable {mapping : InputMap old new} {g : SourceWithEntry old entrySigs sigs} {targets : Checked.Phi.Targets}

/-- A successful width check certifies the original table and the actual emitted function. -/
theorem lowerChecked_sound (accepted : lowerChecked mapping g = some targets) :
    (∃ before, Table.lowerChecked g = some before) ∧ (lowerFunc (mapCaptures mapping g)).WellFormed ∧
    targets = (⟨[lowerFunc (mapCaptures mapping g)]⟩, Generic.lower (mapCaptures mapping g)) :=
  Proofs.lowerChecked_sound accepted

/-- Target typing uses the new public capture count. -/
theorem lowerChecked_typed (accepted : lowerChecked mapping g = some targets) :
    targets.1.WellFormed ∧ targets.2.HasType (Generic.inputContext (wordSorts new))
      [Generic.packed [.value word]] :=
  Proofs.lowerChecked_typed accepted

/-- All λSSA returns pack the original word at exit zero and preserve the whole memory. -/
theorem lambda_return_iff (accepted : lowerChecked mapping g = some targets) (input : WordTuple new)
    (initial final : Memory) (label : Nat) (payload : Value (Atom model)) :
    Eval (instruction model) (inputEnv model input) targets.2 initial label payload final ↔
      ∃ value : Word, value ∈ g.denote model (mapping.pull input) ∧ label = 0 ∧
        payload = Generic.packResult model (out := word) value ∧ final = initial :=
  Proofs.lambda_return_iff accepted input initial final label payload

/-- Native undefinedness at the pulled valuation is actual λSSA divergence. -/
theorem lambda_diverges_iff (accepted : lowerChecked mapping g = some targets) (input : WordTuple new)
    (initial : Memory) :
    Diverges (instruction model) (.region (inputEnv model input) targets.2 initial) ↔
      g.denote model (mapping.pull input) = Part.none :=
  Proofs.lambda_diverges_iff accepted input initial

end Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width
