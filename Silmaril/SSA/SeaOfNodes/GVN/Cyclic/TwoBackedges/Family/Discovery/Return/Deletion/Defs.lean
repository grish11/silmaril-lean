module

public import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges.Family.Discovery.Return.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Defs

/-! Remove one checked dead header write while keeping both complete feedback banks. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges.Family.Discovery.Return.Deletion

open Diamond (Ty ValueSort dataPorts)
open Pure.SubZero (word)
open Pure.ConstantFold.Comparison (Opcode)
open Quads.Join (Block)
open Quads.Loop.Tail.TwoBackedges (Program)
open RVSDG (Port Tuple)

variable {regs : List (ValueSort Unit)}

def operandsAvoid (destination : Nat) :
    {ports : List (Ty Unit)} → Tuple (Port (dataPorts regs)) ports → Bool
  | _, .nil => true
  | _, .cons head tail => decide (Quads.slot head ≠ destination) && operandsAvoid destination tail

/-- Read operands before checking the write. Stop at the first overwrite.
If the old version survives the block, require its end-of-block check. -/
def safeThrough (destination : Nat) (atEnd : Bool) : Block Opcode regs → Bool
  | [] => atEnd
  | quad :: rest => operandsAvoid destination quad.operands &&
      (decide (Quads.slot quad.dest = destination) || safeThrough destination atEnd rest)

/-- A surviving candidate version must avoid the branch and return uses.
Both feedback blocks must overwrite that version before their full-bank jumps. -/
def terminatorSafe (p : Program Opcode regs word) (destination : Nat) : Bool :=
  decide (Quads.slot p.again ≠ destination) && decide (Quads.slot p.select ≠ destination) &&
    decide (Quads.slot p.result ≠ destination) &&
    safeThrough destination false (p.feedback true) && safeThrough destination false (p.feedback false)

def check (p : Program Opcode regs word) (index : Nat) : Bool :=
  match p.header[index]? with
  | none => false
  | some quad =>
    safeThrough (Quads.slot quad.dest) (terminatorSafe p (Quads.slot quad.dest)) (p.header.drop (index + 1))

def erase (p : Program Opcode regs word) (index : Nat) : Program Opcode regs word :=
  {p with header := p.header.eraseIdx index}

def delete? (p : Program Opcode regs word) (index : Nat) : Option (Program Opcode regs word) :=
  if check p index then some (erase p index) else none

/-- Check the nomination against the actual program produced by return selection. -/
def afterReturn? (p : Program Opcode regs word) (index : Nat) : Option (Program Opcode regs word) :=
  delete? (Return.optimize p) index

end Silmaril.SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges.Family.Discovery.Return.Deletion
