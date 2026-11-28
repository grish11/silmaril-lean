module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.Defs

/-! Remove the excluded feedback block from the specialized quad source. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute

open Diamond (Model Signature ValueSort dataPorts)
open Diamond.SCCP (Fact)
open SeaOfNodes.Loop.SCCP (BankDecidableEq)
open RVSDG (Tuple)

universe u v w

variable {Data : Type u} {Op : Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {out : ValueSort Data}
variable {n k : Nat}

/-- Entry, header and dispatcher keep indices 0, 1 and 2. The selected
feedback block is the only block that can move, to compact index 3. -/
def keptBlock (side : Bool) (index : Fin 4) : Fin 5 :=
  if index = 3 then feedbackBlock side else index.castSucc

def mapDestination (embed : Fin n → Fin k) : Tail.Destination regs out n → Tail.Destination regs out k
  | .jump target => .jump (embed target)
  | .ret port => .ret port

def mapTerminator (embed : Fin n → Fin k) : Tail.Terminator regs out n → Tail.Terminator regs out k
  | .transfer dest => .transfer (mapDestination embed dest)
  | .branch test onTrue onFalse => .branch test (mapDestination embed onTrue) (mapDestination embed onFalse)

/-- The compact header has the entry jump and one feedback jump. -/
def predecessor : SeaOfNodes.Loop.Incoming → Fin 4
  | .entry => 0
  | .backedge => 3

def originalOccurrence (side : Bool) : SeaOfNodes.Loop.Incoming → Incoming
  | .entry => .entry
  | .backedge => .feedback side

def originalPredecessor : Incoming → Fin 5
  | .entry => 0
  | .feedback side => feedbackBlock side

variable {m : Model.{u, v, w} Op} {p : Program Op regs out} [BankDecidableEq m.value (dataPorts regs)]
variable {input : Tuple (Fact m.value) (dataPorts regs)}

/-- Reuse each retained body from the specialized source, with all jumps
typed against the four live indices. Dispatch still costs one block visit. -/
def compact (checked : Checked m p input) : Tail.Source Op regs out 4 :=
  fun index =>
    ⟨(checked.source (keptBlock checked.side index)).body,
      if index = 0 then .transfer (.jump 1)
      else if index = 1 then .branch p.again (.jump 2) (.ret p.result)
      else if index = 2 then .transfer (.jump 3)
      else .transfer (.jump 1)⟩

/-- The singleton check is the only admission path. -/
def rewrite (m : Model.{u, v, w} Op) (p : Program Op regs out)
    [BankDecidableEq m.value (dataPorts regs)] (input : Tuple (Fact m.value) (dataPorts regs)) :
    Option (Tail.Source Op regs out 4) :=
  (check m p input).map compact

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute
