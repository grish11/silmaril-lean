module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.Defs
public import Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF.Defs

/-! # Emit the checked quad diamond loop as typed MLIR CF -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF

open SeaOfNodes.Diamond (Val ValueSort dataPorts sortValue)
open SeaOfNodes.Loop.MLIR.CF (Op TargetOp model opcode)
open SeaOfNodes.MLIR (Word)
open SeaOfNodes.MLIR.Lowering (Names Scope encodeValues lowerCode operands valueBits valueWidth weaken)
open Silmaril.MLIR.Arith (Width Env)
open Silmaril.MLIR.CF (Cfg Edge Frame)
open RVSDG (Locals Tuple Wires)
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

def returnFrame {Labels : List Width → Type} (exit : Labels [valueWidth out])
    (value : sortValue Word out) : Frame Labels :=
  ⟨exit, .cons (valueBits value) .nil⟩

def exitFrame (value : sortValue Word out) : Frame (Label regs out size) :=
  returnFrame .exit value

def destinationFrameWith {Labels : List Width → Type}
    (jump : Fin size → Bank (regs := regs) model → Frame Labels)
    (ret : sortValue Word out → Frame Labels) (bank : Bank (regs := regs) model) :
    Destination regs out size → Frame Labels
  | .jump id => jump id bank
  | .ret result => ret (bank.get result)

def destinationFrame (bank : Bank (regs := regs) model)
    (dest : Destination regs out size) : Frame (Label regs out size) :=
  destinationFrameWith siteFrame exitFrame bank dest

/-- Resolve a jump using the calling block's final versions. The destination
chooses its own typed argument bank. -/
abbrev JumpTo (regs : List (ValueSort Width)) (size : Nat) (Labels : List Width → Type) :=
  ∀ {args : List (SeaOfNodes.Diamond.Ty Width)} {past : List (List (SeaOfNodes.Diamond.Ty Width))}
    {Γ : List Width}, Scope args past Γ → Wires args past (dataPorts regs) → Fin size → Edge Labels Γ

abbrev JumpAgrees {Labels : List Width → Type} (jump : JumpTo regs size Labels)
    (frame : Fin size → Bank (regs := regs) model → Frame Labels) : Prop :=
  ∀ {args : List (SeaOfNodes.Diamond.Ty Width)} {past : List (List (SeaOfNodes.Diamond.Ty Width))}
    {Γ : List Width} {scope : Scope args past Γ} {env : Env Γ}
    {input : Tuple (Val Word) args} {locals : Locals (Val Word) past},
    scope.Agrees env input locals → ∀ (versions : Wires args past (dataPorts regs)) (id : Fin size),
      (jump scope versions id).eval env = frame id (versions.read input locals)

variable {Γ : List Width} {args : List (SeaOfNodes.Diamond.Ty Width)}
variable {past : List (List (SeaOfNodes.Diamond.Ty Width))} {Labels : List Width → Type}

def lowerDestinationWith (jump : JumpTo regs size Labels) (exit : Labels [valueWidth out])
    (scope : Scope args past Γ) (versions : Wires args past (dataPorts regs)) :
    Destination regs out size → Edge Labels Γ
  | .jump id => jump scope versions id
  | .ret result => ⟨exit, .cons (scope.resolveValue (versions.get result)) .nil⟩

def lowerTerminatorWith (jump : JumpTo regs size Labels) (exit : Labels [valueWidth out])
    (scope : Scope args past Γ) (versions : Wires args past (dataPorts regs)) :
    Tail.Terminator regs out size → Silmaril.MLIR.CF.Terminator Labels [valueWidth out] Γ
  | .transfer dest => .br (lowerDestinationWith jump exit scope versions dest)
  | .branch test yes no => .condBr (scope.resolveValue (versions.get test))
      (lowerDestinationWith jump exit scope versions yes) (lowerDestinationWith jump exit scope versions no)

def fullJump : JumpTo regs size (Label regs out size) :=
  fun scope versions id => ⟨.site id, operands scope versions⟩

def lowerDestination (scope : Scope (dataPorts regs) past Γ)
    (versions : Wires (dataPorts regs) past (dataPorts regs))
    (dest : Destination regs out size) : Edge (Label regs out size) Γ :=
  lowerDestinationWith fullJump .exit scope versions dest

def lowerTerminator (scope : Scope (dataPorts regs) past Γ)
    (versions : Wires (dataPorts regs) past (dataPorts regs))
    (term : Tail.Terminator regs out size) : Silmaril.MLIR.CF.Terminator (Label regs out size) [valueWidth out] Γ :=
  lowerTerminatorWith fullJump .exit scope versions term

/-- Reuse the ordered quad reaching-version compiler and the existing
Sea of Nodes scalar producer emitter. -/
def lowerBlockWith (jump : JumpTo regs size Labels) (exit : Labels [valueWidth out])
    (block : SourceBlock Op regs out size) (scope : Scope (dataPorts regs) [] Γ) :
    Silmaril.MLIR.CF.Block TargetOp Labels Γ [valueWidth out] :=
  let compiled := CFG.compileBlock block.body (initial regs)
  lowerCode opcode compiled.flow scope fun final =>
    lowerTerminatorWith jump exit final compiled.outgoing block.terminator

def lowerBlock (block : SourceBlock Op regs out size) (scope : Scope (dataPorts regs) [] Γ) :
    Silmaril.MLIR.CF.Block TargetOp (Label regs out size) Γ [valueWidth out] :=
  lowerBlockWith fullJump .exit block scope

variable {src : Source Op regs out size} {entry : Fin size}

/-- Emit a checked diamond with the original block IDs. The external entry
executes the source preheader. No checked edge targets its labeled copy. -/
def lower (_p : Program src entry) : Target regs out size where
  entry := lowerBlock (src entry) ⟨entryNames regs, PUnit.unit⟩
  block
    | .site id => lowerBlock (src id) ⟨blockNames (Widths regs) regs, PUnit.unit⟩
    | .exit => .terminator (.ret (.cons .here .nil))

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF
