module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Defs

/-! Emit the checked header-tested quad loop as typed MLIR CF. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.MLIR.CF

open SeaOfNodes.Diamond (ValueSort dataPorts)
open SeaOfNodes.Diamond.SCCP (Fact)
open SeaOfNodes.Loop.SCCP (BankDecidableEq)
open SeaOfNodes.Loop.MLIR.CF (Op TargetOp model)
open SeaOfNodes.MLIR (Word)
open SeaOfNodes.MLIR.Lowering (encodeValues operands)
open Tail.Diamond.MLIR.CF (Widths JumpTo entryNames blockNames lowerBlockWith)
open Silmaril.MLIR.Arith (Width)
open Silmaril.MLIR.CF (Cfg Frame)
open Blocks (Bank)
open RVSDG (Tuple)

/-- The external entry has no label. Header and feedback carry the complete
typed bank, and the return block takes a single result word. -/
inductive Label (regs : List (ValueSort Width)) (result : Width) : List Width → Type where
  | header : Label regs result (Widths regs)
  | feedback : Label regs result (Widths regs)
  | exit : Label regs result [result]

abbrev Target (regs : List (ValueSort Width)) (result : Width) :=
  Cfg TargetOp (Label regs result) (Widths regs) [result]

variable {regs : List (ValueSort Width)} {result : Width}

/-- Only source indices 1 and 2 can be jump destinations. -/
def siteLabel (id : Fin 3) : Label regs result (Widths regs) :=
  if id = 2 then .feedback else .header

def siteFrame (id : Fin 3) (bank : Bank (regs := regs) model) : Frame (Label regs result) :=
  ⟨siteLabel id, encodeValues bank⟩

def jump : JumpTo regs 3 (Label regs result) :=
  fun scope versions id => ⟨siteLabel id, operands scope versions⟩

variable {p : Program Op regs (.data result)} [BankDecidableEq Word (dataPorts regs)]
variable {facts : Tuple (Fact Word) (dataPorts regs)}

/-- Compile the retained preheader, header and selected feedback body with
the shared quad emitter. The false header edge goes directly to CF return. -/
def lower (checked : Checked model p facts) : Target regs result :=
  let src := bypass checked
  { entry := lowerBlockWith jump .exit (src 0) ⟨entryNames regs, PUnit.unit⟩
    block := fun
      | .header => lowerBlockWith jump .exit (src 1) ⟨blockNames (Widths regs) regs, PUnit.unit⟩
      | .feedback => lowerBlockWith jump .exit (src 2) ⟨blockNames (Widths regs) regs, PUnit.unit⟩
      | .exit => .terminator (.ret (.cons .here .nil)) }

/-- Check the SCCP entry contract for a unique feedback route and emit the
bypassed source. Concrete inputs are related by `TupleCovers`. -/
def compile (p : Program Op regs (.data result)) (facts : Tuple (Fact Word) (dataPorts regs)) :
    Option (Target regs result) :=
  (check model p facts).map lower

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.MLIR.CF
