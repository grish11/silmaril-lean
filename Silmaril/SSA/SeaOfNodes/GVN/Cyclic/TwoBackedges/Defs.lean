module

public import Silmaril.SSA.SeaOfNodes.GVN.WordNumber.Defs
public import Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.Comparison.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Defs

/-! Check one nominated carried equality over both native feedback occurrences. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges

open Diamond (Model Val ValueSort dataPorts)
open Pure.SubZero (word wordPort)
open Pure.ConstantFold.Comparison (Opcode)
open Quads (write)
open Quads.Loop.Tail.TwoBackedges (Program)
open RVSDG (Port Tuple)

abbrev WordSlot (regs : List (ValueSort Unit)) := Port (dataPorts regs) wordPort

abbrev Keys (regs : List (ValueSort Unit)) :=
  Tuple (Val (WordNumber.numbering (dataPorts regs)).value) (dataPorts regs)

/-- Run the same quad evaluator on word keys. Predicate results cannot
feed a word producer in this opcode family. The checker examines both
feedback blocks, so placeholder predicate keys never decide a route. -/
def numbering (regs : List (ValueSort Unit)) : Model Opcode where
  value := (WordNumber.numbering (dataPorts regs)).value
  run
    | .arithmetic op, operands => (WordNumber.numbering (dataPorts regs)).run op operands
    | .boolean _, _ | .eq, _ | .slt, _ | .sle, _ | .not, _ => ⟨false⟩

variable {regs : List (ValueSort Unit)}

/-- Only the nominated member uses another slot's key. Every other word
retains its own typed argument position. -/
def headerKeys (representative member : WordSlot regs) : Keys regs :=
  write member (.argument representative) (WordNumber.entryKeys regs)

def entryMatches (p : Program Opcode regs word) (representative member : WordSlot regs) : Bool :=
  let keys := p.preheader.eval (numbering regs) (WordNumber.entryKeys regs)
  (keys.get representative).matches (keys.get member)

def feedbackMatches (p : Program Opcode regs word) (representative member : WordSlot regs)
    (side : Bool) : Bool :=
  let header := p.header.eval (numbering regs) (headerKeys representative member)
  let keys := (p.feedback side).eval (numbering regs) header
  (keys.get representative).matches (keys.get member)

def exitMatches (p : Program Opcode regs word) (representative member replacement : WordSlot regs) : Bool :=
  let keys := p.header.eval (numbering regs) (headerKeys representative member)
  (keys.get p.result).matches (keys.get replacement)

/-- An inductively justified carried equality may justify a different
pair of equal word reads at the actual post-header return. -/
def check (p : Program Opcode regs word) (representative member replacement : WordSlot regs) : Bool :=
  entryMatches p representative member &&
    feedbackMatches p representative member true &&
    feedbackMatches p representative member false &&
    exitMatches p representative member replacement

/-- Redirect only the return operand. Keep the full bank and both feedback blocks. -/
def rewrite? (p : Program Opcode regs word) (representative member replacement : WordSlot regs) :
    Option (Program Opcode regs word) :=
  if check p representative member replacement then some {p with result := replacement}
  else none

end Silmaril.SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges
