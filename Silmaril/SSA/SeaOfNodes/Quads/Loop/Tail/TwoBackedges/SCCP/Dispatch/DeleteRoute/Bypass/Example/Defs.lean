module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.Example.Defs
public import Silmaril.SSA.SeaOfNodes.Loop.SCCP.Example.Defs

/-! Inspect the retained blocks and the two native block budgets. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Example

open Diamond (Model Ty Val dataPorts)
open Diamond.SCCP (Fact)
open SeaOfNodes.Loop.SCCP (BankDecidableEq)
open RVSDG (Port Tuple)
open SCCP.Example (Byte regs word model program facts concrete)
open Dispatch.Example (looping)
open Semantics.Dataflow (Flat)

def originalBlocks (side : Flat (ULift Bool)) : Option (List Nat) :=
  (check model program (facts side)).map fun checked =>
    (List.finRange 3).map fun i => (keptBlock checked.side (retainedBlock i)).val

/-- Run the two check-dependent sources at the same numeric fuel so the
difference in their minimum budgets is visible. -/
def returnPair (side : Bool) (fuel : Nat) : Option (Option Nat × Option Nat) :=
  let input := facts (.constant ⟨side⟩)
  (check model program input).map fun (checked : Checked model program input) =>
    (((compact checked).runFrom model fuel 0 (concrete side)).map BitVec.toNat,
      ((bypass checked).runFrom model fuel 0 (concrete side)).map BitVec.toNat)

/-- The entry contract permits immediate exit and only false feedback. -/
def immediateExit (fuel : Nat) : Option (Option Nat × Option Nat) :=
  let input : Tuple (Fact model.value) (dataPorts regs) :=
    .cons .overdefined (.cons (.constant ⟨false⟩) (.cons (.constant (7 : Byte)) .nil))
  let entry : Tuple (Val model.value) (dataPorts regs) := .cons ⟨false⟩ (.cons ⟨false⟩ (.cons (7 : Byte) .nil))
  (check model program input).map fun (checked : Checked model program input) =>
    (((compact checked).runFrom model fuel 0 entry).map BitVec.toNat,
      ((bypass checked).runFrom model fuel 0 entry).map BitVec.toNat)

abbrev RepeatOp := SeaOfNodes.Loop.SCCP.Example.Op
abbrev repeatModel : Model RepeatOp := SeaOfNodes.Loop.SCCP.Example.model

instance repeatBankEq : BankDecidableEq repeatModel.value (dataPorts regs) := SCCP.Example.bankEq

def bytePort : Port (dataPorts regs) (.value word) := .tail (.tail .head)

/-- Start the byte at one, then increment it on feedback until the
post-header test sees three. The native run takes two feedback jumps. -/
def repeatProgram : Program RepeatOp regs word where
  preheader := []
  header := [⟨[word, .predicate], .predicate, .head, .continues, .cons bytePort (.cons .head .nil)⟩]
  again := .head
  select := .tail .head
  result := bytePort
  feedback _ := [⟨[word], word, bytePort, .advance 1, .cons bytePort .nil⟩]

def repeatEntry : Tuple (Val repeatModel.value) (dataPorts regs) :=
  .cons ⟨true⟩ (.cons ⟨false⟩ (.cons (1 : Byte) .nil))

def repeatFacts : Tuple (Fact repeatModel.value) (dataPorts regs) :=
  .cons (.constant ⟨true⟩) (.cons (.constant ⟨false⟩) (.cons (.constant (1 : Byte)) .nil))

def repeatPair (fuel : Nat) : Option (Option Nat × Option Nat) :=
  (check repeatModel repeatProgram repeatFacts).map fun (checked : Checked repeatModel repeatProgram repeatFacts) =>
    (((compact checked).runFrom repeatModel fuel 0 repeatEntry).map BitVec.toNat,
      ((bypass checked).runFrom repeatModel fuel 0 repeatEntry).map BitVec.toNat)

def loopPair (fuel : Nat) : Option (Option Nat × Option Nat) :=
  let input := facts (.constant ⟨false⟩)
  (check model looping input).map fun (checked : Checked model looping input) =>
    (((compact checked).runFrom model fuel 0 (concrete false)).map BitVec.toNat,
      ((bypass checked).runFrom model fuel 0 (concrete false)).map BitVec.toNat)

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Example
