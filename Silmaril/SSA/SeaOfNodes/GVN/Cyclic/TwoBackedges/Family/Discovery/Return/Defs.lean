module

public import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges.Family.Discovery.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.CFG.Defs
public import Silmaril.SSA.RVSDG.Isomorphism.Defs

/-! Select and check a canonical returned carried word in the native two-feedback loop. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges.Family.Discovery.Return

open Diamond (ValueSort dataPorts)
open Pure.SubZero (word wordPort)
open Pure.ConstantFold.Comparison (Opcode)
open Quads.Loop.Tail.TwoBackedges (Program)
open RVSDG (Address Origin extend)
open TwoBackedges (WordSlot)

variable {regs : List (ValueSort Unit)}

/-- The actual reaching version read by the return after executing the header. -/
def returnOrigin (p : Program Opcode regs word) :
    Origin (dataPorts regs) (extend [] p.header.producers) wordPort :=
  (Quads.CFG.compileBlock p.header (Quads.initial regs)).outgoing.get p.result

/-- Admit a direct read of the original carried argument. A header-produced
version of the same register is outside this policy. -/
def returnedLane? (p : Program Opcode regs word) : Option (Lane regs) :=
  if (returnOrigin p).address = .arg p.result.index then
    (List.finRange (slots regs).length).find? fun i => decide ((slot i).index = p.result.index)
  else none

def Eligible (p : Program Opcode regs word) (classes : Classes regs) (original candidate : Lane regs) : Prop :=
  classes original = classes candidate ∧ Family.exitMatches p (equations classes) (slot candidate) = true

/-- Search the actual word slots in original register order. A shared header
evaluation supplies the exit keys, including any overwritten slots. -/
def best (p : Program Opcode regs word) (classes : Classes regs) (original : Lane regs) : Lane regs :=
  let keys := Family.headerKeys p (equations classes)
  let resultKey := keys.get p.result
  ((List.finRange (slots regs).length).find? fun candidate =>
    decide (classes original = classes candidate) && resultKey.matches (keys.get (slot candidate))).getD original

def representative? (p : Program Opcode regs word) : Option (WordSlot regs) :=
  (returnedLane? p).map fun original => slot (best p (normalize p) original)

/-- Select a return representative and run the existing family checker before
emitting it. Preserve the original native program for non-carried and canonical returns. -/
def optimize (p : Program Opcode regs word) : Program Opcode regs word :=
  match returnedLane? p with
  | none => p
  | some original =>
    let classes := normalize p
    let candidate := best p classes original
    if candidate = original then p
    else (Family.rewrite? p (equations classes) (slot candidate)).getD p

end Silmaril.SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges.Family.Discovery.Return
