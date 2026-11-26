module

public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Defs

/-! A shared checked producer table with two feedback successor occurrences. -/

@[expose] public section

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch

open Silmaril.Machine.Lir (Word Memory)
open Silmaril.Machine.RTL (Frame)
open Silmaril.Machine.RTL.SSA (Block Func Prog StepsNWithin step)
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (PortTy Reg model)
open Silmaril.SSA.RVSDG (Origin Wires extend)
open Silmaril.SSA.SeaOfNodes.Diamond (read)
open Silmaril.SSA.SeaOfNodes.Loop (appendTuple)

variable {captures bank old new : Nat} {entrySigs sigs : List (List PortTy)}

abbrev HeaderWord (captures bank : Nat) (sigs : List (List PortTy)) :=
  Origin (wordPorts captures ++ wordPorts bank) (extend [] sigs) wordPort

abbrev Feedback (captures bank : Nat) (sigs : List (List PortTy)) :=
  Wires (wordPorts captures ++ wordPorts bank) (extend [] sigs) (wordPorts bank)

/-- Both feedback columns use the same typed header snapshot. The primary
row provides the existing entry Φ, continuation predicate, and exit word. -/
structure Source (captures bank : Nat) (entrySigs sigs : List (List PortTy)) where
  primary : Width.Source captures bank entrySigs sigs
  other : Feedback captures bank sigs
  selector : HeaderWord captures bank sigs

variable (p : Source captures bank entrySigs sigs)

/-- Each dispatch arm has an ordinary native guarded-row projection. -/
def Source.row (side : Bool) : Width.Source captures bank entrySigs sigs :=
  if side then p.primary else
    { p.primary with
      phiInputs
        | .entry => p.primary.phiInputs .entry
        | .backedge => p.other }

def Source.column (side : Bool) : Feedback captures bank sigs := (p.row side).phiInputs .backedge

/-- On a continuing visit the independent word selector chooses the Φ column. -/
def Source.side (input : WordTuple captures) (carried : WordTuple bank) : Bool :=
  let args := appendTuple carried input
  let locals := p.primary.header.eval model args PUnit.unit
  let value : Word := read model p.selector args locals
  decide (value ≠ (0 : Word))

/-- The native visit reuses the guarded-row step and retains the selected arm. -/
def Source.step (input : WordTuple captures) (carried : WordTuple bank) :
    Word ⊕ (Bool × WordTuple bank) :=
  let side := p.side input carried
  match (p.row side).step model input carried with
  | .inl value => .inl value
  | .inr next => .inr (side, next)

/-- Finite native returns counted by completed feedback transfers. -/
inductive Source.ReturnsAfter (input : WordTuple captures) : Nat → WordTuple bank → Word → Prop
  | exit {carried value} (taken : p.step input carried = .inl value) :
      ReturnsAfter input 0 carried value
  | feedback {count carried side next value} (taken : p.step input carried = .inr (side, next))
      (rest : ReturnsAfter input count next value) :
      ReturnsAfter input (count + 1) carried value

def mapCaptures (mapping : InputMap old new) (p : Source old bank entrySigs sigs) :
    Source new bank entrySigs sigs where
  primary := Width.mapCaptures mapping p.primary
  other := mapColumn (fun port => Width.headerPort mapping port) p.other
  selector := mapOrigin (fun port => Width.headerPort mapping port) p.selector

/-- The two transfers have the same target and different successor indices. -/
def feedbackSlot (side : Bool) : Fin 2 := if side then 0 else 1

def header : Block Reg :=
  { Width.header p.primary with
    term := .cond (register p.primary.predicate.address) 3 [] 2 [register p.primary.result.address] }

def dispatch : Block Reg :=
  ⟨[], [], .cond (register p.selector.address) 1 (emitColumn (p.column true))
    1 (emitColumn (p.column false))⟩

def lowerFunc : Func Reg :=
  ⟨⟨captures, 1⟩, 0, [Width.preheader p.primary, header p, exitBlock, dispatch p]⟩

def lowerRTL : Prog Reg := ⟨[lowerFunc p]⟩

/-- Exact boundary of one visit. The exit uses one return instruction after
the header branch. Feedback uses one dispatch instruction after the header
branch and observes the selected successor slot in the pre-transfer frame. -/
def Activation (prog : Prog Reg) (input : WordTuple captures) (fr : Frame Reg) (mem : Memory)
    (outcome : Word ⊕ (Bool × WordTuple bank)) : Prop :=
    match outcome with
    | .inl value =>
      ∃ ready, StepsNWithin prog [] (sigs.length + 1) ⟨⟨0, 1, 0⟩, fr, [], mem⟩
        ⟨⟨0, 2, 0⟩, ready, [], mem⟩ ∧
        step prog ⟨⟨0, 2, 0⟩, ready, [], mem⟩ = .returned [value] mem
    | .inr (side, values) =>
      ∃ ready latched, StepsNWithin prog [] (sigs.length + 1) ⟨⟨0, 1, 0⟩, fr, [], mem⟩
        ⟨⟨0, 3, 0⟩, ready, [], mem⟩ ∧
        prog.fetch ⟨0, 3, 0⟩ = some (.term (dispatch p).term) ∧
        (ready.get (register p.selector.address)).map
          (fun value => feedbackSlot (decide (value ≠ (0 : Word)))) = some (feedbackSlot side) ∧
        ((dispatch p).term.args)[(feedbackSlot side).val]? = some (1, emitColumn (p.column side)) ∧
        ready.readAll (emitColumn (p.column side)) = some (words values) ∧
        step prog ⟨⟨0, 3, 0⟩, ready, [], mem⟩ =
          .running ⟨⟨0, 1, 0⟩, latched, [], mem⟩ ∧
        ArgsMatch latched (appendTuple values input)

/-- After entry, a continuing visit ends in the dispatch transfer and a
returning visit ends in the return instruction. Both cost the same. -/
def rtlFuel (entrySigs sigs : List (List PortTy)) (backedges : Nat) : Nat :=
  entrySigs.length + 1 + (sigs.length + 2) * (backedges + 1)

/-- Validate each native row with the existing checker, then run the ordinary
machine checker on the actual merged CFG and resized entry interface. -/
def lowerChecked (mapping : InputMap old new) (p : Source old old entrySigs sigs) :
    Option (Prog Reg) := do
  let _ ← Table.lowerChecked (p.row true)
  let _ ← Table.lowerChecked (p.row false)
  let mapped := mapCaptures mapping p
  if (lowerFunc mapped).WellFormed then some (lowerRTL mapped) else none

end Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch
