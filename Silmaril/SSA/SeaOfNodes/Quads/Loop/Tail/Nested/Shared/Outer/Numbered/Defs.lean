module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Numbered.Execution.Defs

/-! # Numbered γ/θ with shared continuations at the inner and outer merges -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered

open SeaOfNodes.Diamond (Model Ty ValueSort dataPorts)
open RVSDG (Wires extend)
open RVSDG.NestedTheta (Term)
open Join (Block Opcode)
open Nested.Numbered (splitSigs)
open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond (bodyPorts thenBase routeLatchWith)
open Blocks (Bank)

universe u v w

variable {Data : Type u} {Op : SeaOfNodes.Diamond.Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {out : ValueSort Data} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size} (p : Program src entry)

abbrev outerScope :=
  extend (extend [] (src p.header).body.producers) (splitSigs regs)

abbrev mergeScope :=
  extend (outerScope p) p.outerSuffix.quads.producers

/-- Compile the one outer suffix against the actual outer γ result wires. -/
def afterOuterSuffix {results : List (Ty Data)} {suffix : List (List (Ty Data))}
    (finish : Wires (dataPorts regs) (mergeScope p) (dataPorts regs) →
      Term (Opcode Op) (dataPorts regs) (mergeScope p) suffix results) :
    Term (Opcode Op) (dataPorts regs) []
      ((src p.header).body.producers ++ (splitSigs regs ++ (p.outerSuffix.quads.producers ++ suffix))) results :=
  Prefix.afterHeader p.toRoutes fun merged => thenBase (p.outerSuffix.quads.lowerFrom merged .jump) finish

/-- Observe the emitted outer γ before its shared suffix. -/
def outerRegion : Term (Opcode Op) (dataPorts regs) []
    ((src p.header).body.producers ++ splitSigs regs) (dataPorts regs) :=
  Prefix.afterHeader p.toRoutes .ret

/-- Observe the actual wiring at the original final merge boundary. -/
def mergeRegion : Term (Opcode Op) (dataPorts regs) []
    ((src p.header).body.producers ++ (splitSigs regs ++ (p.outerSuffix.quads.producers ++ []))) (dataPorts regs) :=
  afterOuterSuffix p .ret

def tail : Block Op regs := (src p.join).body ++ (src p.latch).body

abbrev selectedBank (m : Model.{u, v, w} Op) (old : Bank (regs := regs) m) :=
  p.mergeBank m old (p.toControl.selected m old)

abbrev selectedVisits (m : Model.{u, v, w} Op) (old : Bank (regs := regs) m) :=
  p.mergeVisits (p.toControl.selected m old)

def nextBank (m : Model.{u, v, w} Op) (old : Bank (regs := regs) m) : Bank (regs := regs) m :=
  Shared.Numbered.Execution.nextBank p.toControl m (selectedBank p m) old

def sourceVisits (m : Model.{u, v, w} Op) (fuel : Nat) (input : Bank (regs := regs) m) : Nat :=
  Shared.Numbered.Execution.sourceVisits p.toControl m (selectedBank p m) (selectedVisits p m) fuel input

abbrev bodySigs :=
  (src p.header).body.producers ++ (splitSigs regs ++ (p.outerSuffix.quads.producers ++ ((tail p).producers ++ [bodyPorts regs])))

def thetaBody : Term (Opcode Op) (dataPorts regs) [] (bodySigs p) (bodyPorts regs) :=
  afterOuterSuffix p fun merged =>
    thenBase ((tail p).lowerFrom merged .jump) (routeLatchWith p.again)

def lower : RVSDG.NestedTheta.Graph (Opcode Op) (dataPorts regs) []
    ((src entry).body.producers ++ [dataPorts regs]) [.value out] :=
  Shared.Numbered.Execution.lower p.toControl (thetaBody p)

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered
