module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Prefix.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.MLIR.CF.Phi.Readback.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Chain.Segment.Incoming.Defs

/-! # Read the actual inner-tail Φ columns of either shared-tail profile -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.MLIR.CF.InnerPhi

open SeaOfNodes.Diamond (Ty ValueSort dataPorts)
open SeaOfNodes.Loop.MLIR.CF (Op model)
open SeaOfNodes.MLIR.Lowering (encodeValues)
open Silmaril.MLIR.Arith (Env Width)
open Silmaril.MLIR.CF (Edge Frame)
open Silmaril.MLIR.Pure (Operands)
open Outer.MLIR.CF.Phi (Types arguments atTarget terminal terminalEnv)
open Outer.MLIR.CF.Phi.Readback (successor)
open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond (thenBase)
open Diamond.MLIR.CF (Label Widths lowerSource)
open Join (Opcode)
open RVSDG (Wires extend)
open RVSDG.NestedTheta (Term)
open Blocks (Bank)

variable {regs : List (ValueSort Width)} {out : ValueSort Width} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size} (p : Prefix.Routes src entry)

def armStart (taken : Bool) : Fin size := if taken then p.onInnerTrue else p.onInnerFalse

def arm : (taken : Bool) → Chain.Segment src p.meet (armStart p taken)
  | true => p.innerTrue
  | false => p.innerFalse

def occurrence (taken : Bool) : Occurrence := if taken then .innerTrue else .innerFalse

/-- Exactly the full-bank emitter used by the legacy and outer profiles. -/
abbrev cfg (_plan : Prefix.Routes src entry) := lowerSource src entry

def predecessor (taken : Bool) :=
  (cfg p).block (.site (p.innerEdgeOccurrence taken).1)

abbrev Scope (taken : Bool) := (terminal (predecessor p taken)).1

/-- Inspect the original raw slot before checking its destination. Both
slots of a direct inner conditional can legitimately enter the same tail. -/
def incoming (taken : Bool) : Option (Operands (Scope p taken) (Widths regs)) :=
  (successor (p.innerEdgeOccurrence taken).2 (terminal (predecessor p taken)).2).bind (atTarget p.meet)

structure Rows where
  operands : (taken : Bool) → Operands (Scope p taken) (Widths regs)
  checked : ∀ taken, incoming p taken = some (operands taken)

def readRows : Option (Rows p) :=
  if checked : (incoming p true).isSome ∧ (incoming p false).isSome then
    let present (taken : Bool) : (incoming p taken).isSome :=
      match taken with | true => checked.1 | false => checked.2
    some ⟨fun taken => (incoming p taken).get (present taken), fun taken => (Option.some_get (present taken)).symm⟩
  else none

def headerBank (old : Bank (regs := regs) model) := (src p.header).body.eval model old

def splitBank (old : Bank (regs := regs) model) := (src p.inner).body.eval model (headerBank p old)

def side (old : Bank (regs := regs) model) : Bool := ((splitBank p old).get p.innerTest).down

def beforePredecessor (taken : Bool) (old : Bank (regs := regs) model) : Bank (regs := regs) model :=
  (arm p taken).predecessorBank model (headerBank p old) (splitBank p old)

def arrivalEnv (taken : Bool) (input old : Bank (regs := regs) model) : Env (Scope p taken) :=
  terminalEnv (predecessor p taken) ((encodeValues (beforePredecessor p taken old)).append (encodeValues input))

abbrev gammaScope := extend (extend [] (src p.inner).body.producers) (Prefix.innerPlan p).producers

/-- The existing inner-arm lowering, exposing its continuation at the
place where the γ result wires feed the shared suffix. -/
def afterInner {results : List (SeaOfNodes.Diamond.Ty Width)} {suffix : List (List (SeaOfNodes.Diamond.Ty Width))}
    (finish : Wires (dataPorts regs) (gammaScope p) (dataPorts regs) →
      Term (Opcode Op) (dataPorts regs) (gammaScope p) suffix results) :
    Term (Opcode Op) (dataPorts regs) []
      ((src p.inner).body.producers ++ ((Prefix.innerPlan p).producers ++ suffix)) results :=
  thenBase ((src p.inner).body.lowerFrom (initial regs) .jump) fun current =>
    thenBase ((Prefix.innerPlan p).lowerFrom current) finish

/-- Read the real inner γ result wires in place of running their continuation. -/
def gamma := (afterInner p .ret).toGraph

variable {p}

def Rows.terminators (rows : Rows p) (taken : Bool) : Isotope.LambdaSSA.Terminator Silmaril.MLIR.Arith.Prim :=
  .br p.meet.val (PhiView.packTerm (arguments (rows.operands taken)))

def Rows.typing (rows : Rows p) : PhiView.SourceTyping (τ := Silmaril.Ty Width) rows.terminators where
  context taken := Types (Scope p taken)
  cases _ := .jump

def Rows.view (rows : Rows p) : PhiView.View rows.typing (Outer.MLIR.CF.Phi.parameters (regs := regs)) :=
  PhiView.ofBlockArgs (fun ⟨taken, .jump⟩ => ⟨arguments (rows.operands taken), rfl⟩)

def Rows.edge (rows : Rows p) (taken : Bool) : PhiView.EdgeOcc rows.terminators :=
  ⟨taken, .jump⟩

def Rows.rebuild (rows : Rows p) (taken : Bool) : Edge (Label regs out size) (Scope p taken) :=
  ⟨.site p.meet, Outer.MLIR.CF.Phi.Readback.operands ((PhiView.toBlockArgs rows.view (rows.edge taken)).val)⟩

def Rows.bank (rows : Rows p) (taken : Bool) (input old : Bank (regs := regs) model) : Env (Widths regs) :=
  (rows.rebuild taken).args.eval (arrivalEnv p taken input old)

def Rows.frame (rows : Rows p) (taken : Bool) (input old : Bank (regs := regs) model) : Frame (Label regs out size) :=
  ⟨.site p.meet, rows.bank taken input old⟩

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.MLIR.CF.InnerPhi
