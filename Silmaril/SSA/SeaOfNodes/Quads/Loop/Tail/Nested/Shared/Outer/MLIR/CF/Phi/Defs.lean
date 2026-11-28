module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.MLIR.CF.Defs
public import Silmaril.SSA.PhiView.Defs

/-! # The actual CF operands as positional Φ columns at the shared outer tail -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.MLIR.CF.Phi

open SeaOfNodes.Diamond (ValueSort)
open SeaOfNodes.Loop.MLIR.CF (Op TargetOp model evalOp)
open SeaOfNodes.MLIR.Lowering (encodeValues valueWidth)
open Silmaril.MLIR.Arith (Atom Width Env Var word)
open Silmaril.MLIR.CF (Edge Frame Terminator)
open Silmaril.MLIR.Pure (Code Operands)
open Silmaril.Isotope (Value)
open Diamond.MLIR.CF (Label Widths)
open Blocks (Bank)

variable {regs : List (ValueSort Width)} {out : ValueSort Width} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size}
variable {Γ Δ : List Width}

def terminal {Term : List Width → Type} : {Γ : List Width} → Silmaril.MLIR.Pure.Code TargetOp Term Γ →
    (scope : List Width) × Term scope
  | _, .terminator t => ⟨_, t⟩
  | _, .letOp _ _ rest => terminal rest

/-- The environment at the end of the existing pure CF body. -/
def terminalEnv {Term : List Width → Type} : {Γ : List Width} →
    (code : Silmaril.MLIR.Pure.Code TargetOp Term Γ) → Env Γ → Env (terminal code).1
  | _, .terminator _, env => env
  | _, .letOp op args rest, env => terminalEnv rest (.cons (evalOp op (args.eval env)) env)

def atTarget (target : Fin size) : Edge (Label regs out size) Γ → Option (Operands Γ (Widths regs))
  | ⟨.site id, args⟩ => if id = target then some args else none
  | ⟨.exit, _⟩ => none

/-- Read the original successor slot. A conditional predecessor in this
profile has just one branch to the shared tail. -/
def atSlot (target : Fin size) (slot : Fin 2) :
    Silmaril.MLIR.CF.Terminator (Label regs out size) Δ Γ → Option (Operands Γ (Widths regs))
  | .br edge => if slot = 0 then atTarget target edge else none
  | .condBr _ yes no =>
    let (edge, other) := if slot = 0 then (yes, no) else (no, yes)
    if (atTarget target other).isNone then atTarget target edge else none
  | .ret _ => none

variable (p : Program src entry)

/-- The index chooses one of the two original outer predecessors. Both
inner routes use the outer-true occurrence. -/
def predecessor (taken : Bool) :=
  (lower p).block (.site (p.outerEdgeOccurrence taken).1)

abbrev Scope (taken : Bool) := (terminal (predecessor p taken)).1

def incoming (taken : Bool) : Option (Operands (Scope p taken) (Widths regs)) :=
  atSlot p.stop (p.outerEdgeOccurrence taken).2 (terminal (predecessor p taken)).2

/-- Both rows were read from the actual typed CF terminators. -/
structure Rows where
  operands : (taken : Bool) → Operands (Scope p taken) (Widths regs)
  checked : ∀ taken, incoming p taken = some (operands taken)

def readRows : Option (Rows p) :=
  if checked : (incoming p true).isSome ∧ (incoming p false).isSome then
    let present (taken : Bool) : (incoming p taken).isSome :=
      match taken with | true => checked.1 | false => checked.2
    some ⟨fun taken => (incoming p taken).get (present taken),
      fun taken => (Option.some_get (present taken)).symm⟩
  else none

abbrev Types (widths : List Width) := widths.map Silmaril.Ty.base

def operand {w : Width} (v : Var Γ w) : PhiView.Operand (Types Γ) (.base w) :=
  ⟨v.index, by induction v with | here => rfl | there _ ih => exact ih⟩

def arguments : {Δ : List Width} → Operands Γ Δ → PhiView.Arguments (Types Γ) (Types Δ)
  | _, .nil => fun i => (Nat.not_lt_zero _ i.isLt).elim
  | _, .cons v rest => fun i => Fin.cases (operand v) (arguments rest) i

/-- Pack CF values using the existing width-tagged λSSA encoding. -/
def pack : {Δ : List Width} → Env Δ → Value Atom
  | _, .nil => .unit
  | _, .cons value rest => .pair (word value) (pack rest)

variable {p}

def Rows.terminators (rows : Rows p) (taken : Bool) : Isotope.LambdaSSA.Terminator Silmaril.MLIR.Arith.Prim :=
  .br p.stop.val (PhiView.packTerm (arguments (rows.operands taken)))

def Rows.typing (rows : Rows p) : PhiView.SourceTyping (τ := Silmaril.Ty Width) rows.terminators where
  context taken := Types (Scope p taken)
  cases _ := .jump

def parameters (_ : Nat) := Types (Widths regs)

/-- This local Φ view packs only the two checked CF arrivals. The two
source indices retain their original block and slot via outerEdgeOccurrence. -/
def Rows.view (rows : Rows p) : PhiView.View rows.typing (parameters (regs := regs)) :=
  PhiView.ofBlockArgs (fun ⟨taken, .jump⟩ => ⟨arguments (rows.operands taken), rfl⟩)

def Rows.edge (rows : Rows p) (taken : Bool) : PhiView.EdgeOcc rows.terminators :=
  ⟨taken, .jump⟩

def arrivalSide (old : Bank (regs := regs) model) :=
  p.toControl.selected model old != .outerFalse

def arrivalEnv (input old : Bank (regs := regs) model) : Env (Scope p (arrivalSide (p := p) old)) :=
  let occurrence := p.toControl.selected model old
  terminalEnv (predecessor p (arrivalSide (p := p) old))
    ((encodeValues (p.outerPredecessorBank model old occurrence)).append (encodeValues input))

def Rows.selectedBank (rows : Rows p) (input old : Bank (regs := regs) model) : Env (Widths regs) :=
  (rows.operands (arrivalSide (p := p) old)).eval (arrivalEnv (p := p) input old)

def Rows.selectedFrame (rows : Rows p) (input old : Bank (regs := regs) model) : Frame (Label regs out size) :=
  ⟨.site p.stop, rows.selectedBank input old⟩

def Rows.latch (rows : Rows p) (input old : Bank (regs := regs) model) : Value Atom :=
  PhiView.latch rows.view (rows.edge (arrivalSide (p := p) old)) (arrivalEnv (p := p) input old).toLambdaSSA

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.MLIR.CF.Phi
