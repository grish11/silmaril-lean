module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.GuardedTheta.Defs

/-! Emit the original dispatch as γ inside an entry-guarded θ. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Numbered

open SeaOfNodes.Diamond (Signature ValueSort dataPorts)
open RVSDG.NestedTheta (Term Graph)
open Join (Block Opcode)
open Join.Finite (Plan lastBank)
open Tail.Diamond (bodyPorts latchNodeFor thenBase)

universe u v

variable {Data : Type u} {Op : Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {out : ValueSort Data} (p : Program Op regs out)

/-- The inner γ has the original true and false feedback columns in order. -/
def feedbackPlan : Plan Op regs :=
  [⟨p.feedback true, p.feedback false, [], .test p.select (.take 0) (.take 1)⟩]

abbrev BodySigs :=
  (feedbackPlan p).producers ++ (p.header.producers ++ [bodyPorts regs])

/-- Execute the selected feedback body, then the next header and its test. -/
def thetaBody : Term (Opcode Op) (dataPorts regs) [] (BodySigs p) (bodyPorts regs) :=
  thenBase ((feedbackPlan p).lowerFrom (initial regs)) fun feedback =>
    thenBase (p.header.lowerFrom feedback .jump) fun header =>
      .bind (.ofBase (latchNodeFor p.again header)) (fun i => i.elim0)
        (.ret (lastBank _ (bodyPorts regs)))

def entryBlock : Block Op regs := p.preheader ++ p.header

abbrev Target :=
  Graph (Opcode Op) (dataPorts regs) [] ((entryBlock p).producers ++ [bodyPorts regs, [.value out]]) [.value out]

/-- Evaluate the first header before entering θ. A returning header never
evaluates either feedback arm. -/
def lower : Target p := (GuardedTheta.lowerTerm (entryBlock p) p.again p.result (thetaBody p)).toGraph

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Numbered
