module

public import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges.Family.Discovery.Return.Deletion.Defs

/-! Discover and erase dead header writes in the current native two-backedge program. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges.Family.Discovery.Return.Deletion.Cleanup

open Diamond (ValueSort)
open Pure.SubZero (word)
open Pure.ConstantFold.Comparison (Opcode)
open Quads.Loop.Tail.TwoBackedges (Program)

variable {regs : List (ValueSort Unit)}

/-- The least current header index accepted by the checked deletion test. -/
def first? (p : Program Opcode regs word) : Option Nat :=
  (List.range p.header.length).find? (check p)

/-- Erase the write selected by the check on this program. -/
def step? (p : Program Opcode regs word) : Option (Program Opcode regs word) :=
  (first? p).map (erase p)

/-- Spend one unit of fuel per deletion and scan the residual header afresh. -/
def run : Nat → Program Opcode regs word → Program Opcode regs word
  | 0, p => p
  | fuel + 1, p =>
    match step? p with
    | none => p
    | some next => run fuel next

/-- The original header length bounds the number of deletions. -/
def normalize (p : Program Opcode regs word) : Program Opcode regs word :=
  run p.header.length p

/-- Redirect the carried return once, then clean up its actual emitted program. -/
def optimize (p : Program Opcode regs word) : Program Opcode regs word :=
  normalize (Return.optimize p)

end Silmaril.SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges.Family.Discovery.Return.Deletion.Cleanup
