module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.Defs
public import Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF.Defs

/-! # Emit the checked quad diamond loop as typed MLIR CF -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF

open SeaOfNodes.Diamond (ValueSort dataPorts sortValue)
open SeaOfNodes.Loop.MLIR.CF (Op TargetOp model opcode)
open SeaOfNodes.MLIR (Word)
open SeaOfNodes.MLIR.Lowering (Names Scope encodeValues lowerCode operands valueBits valueWidth weaken)
open Silmaril.MLIR.Arith (Width Env)
open Silmaril.MLIR.CF (Cfg Edge Frame)
open RVSDG (Tuple Wires)
open Blocks (Bank)

abbrev Widths (regs : List (ValueSort Width)) := regs.map valueWidth

/-- A successor carries the full register bank, including `i1` predicates.
The typed CF return gets its own label, since `cf.cond_br` takes two edges. -/
inductive Label (regs : List (ValueSort Width)) (out : ValueSort Width) (size : Nat) :
    List Width → Type where
  | site (id : Fin size) : Label regs out size (Widths regs)
  | exit : Label regs out size [valueWidth out]

variable {regs : List (ValueSort Width)} {out : ValueSort Width} {size : Nat}

abbrev Target (regs : List (ValueSort Width)) (out : ValueSort Width) (size : Nat) :=
  Cfg TargetOp (Label regs out size) (Widths regs) [valueWidth out]

/-- Bind the mixed bank in source slot order. -/
def entryNames : (regs : List (ValueSort Width)) → Tuple (Names (Widths regs)) (dataPorts regs)
  | [] => .nil
  | slot :: rest => .cons .here ((entryNames rest).map (weaken (valueWidth slot)))

/-- Successor arguments precede the dominating external inputs. Only the
successor arguments are named by source register reads. -/
def blockNames (extra : List Width) :
    (regs : List (ValueSort Width)) → Tuple (Names (Widths regs ++ extra)) (dataPorts regs)
  | [] => .nil
  | slot :: rest => .cons .here ((blockNames extra rest).map (weaken (valueWidth slot)))

def siteFrame (id : Fin size) (bank : Bank (regs := regs) model) :
    Frame (Label regs out size) :=
  ⟨.site id, encodeValues bank⟩

def exitFrame (value : sortValue Word out) :
    Frame (Label regs out size) :=
  ⟨.exit, .cons (valueBits value) .nil⟩

def destinationFrame (bank : Bank (regs := regs) model) :
    Destination regs out size → Frame (Label regs out size)
  | .jump id => siteFrame id bank
  | .ret result => exitFrame (bank.get result)

variable {Γ : List Width} {past : List (List (SeaOfNodes.Diamond.Ty Width))}

/-- Both occurrences read the predecessor's own outgoing version map. -/
def lowerDestination (scope : Scope (dataPorts regs) past Γ)
    (versions : Wires (dataPorts regs) past (dataPorts regs)) :
    Destination regs out size → Edge (Label regs out size) Γ
  | .jump id => ⟨.site id, operands scope versions⟩
  | .ret result => ⟨.exit, .cons (scope.resolveValue (versions.get result)) .nil⟩

def lowerTerminator (scope : Scope (dataPorts regs) past Γ)
    (versions : Wires (dataPorts regs) past (dataPorts regs)) :
    Tail.Terminator regs out size → Silmaril.MLIR.CF.Terminator (Label regs out size) [valueWidth out] Γ
  | .transfer dest => .br (lowerDestination scope versions dest)
  | .branch test yes no => .condBr (scope.resolveValue (versions.get test))
      (lowerDestination scope versions yes) (lowerDestination scope versions no)

/-- Reuse the ordered quad reaching-version compiler and the existing
Sea of Nodes scalar producer emitter. -/
def lowerBlock (block : SourceBlock Op regs out size) (scope : Scope (dataPorts regs) [] Γ) :
    Silmaril.MLIR.CF.Block TargetOp (Label regs out size) Γ [valueWidth out] :=
  let compiled := CFG.compileBlock block.body (initial regs)
  lowerCode opcode compiled.flow scope fun final =>
    lowerTerminator final compiled.outgoing block.terminator

variable {src : Source Op regs out size} {entry : Fin size}

/-- Emit a checked diamond with the original block IDs. The external entry
executes the source preheader. No checked edge targets its labeled copy. -/
def lower (_p : Program src entry) : Target regs out size where
  entry := lowerBlock (src entry) ⟨entryNames regs, PUnit.unit⟩
  block
    | .site id => lowerBlock (src id) ⟨blockNames (Widths regs) regs, PUnit.unit⟩
    | .exit => .terminator (.ret (.cons .here .nil))

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF
