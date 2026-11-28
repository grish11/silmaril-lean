module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Numbered.Defs

/-! # A smaller common γ output in the checked nested loop -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Numbered

open SeaOfNodes.Diamond (Model Ty ValueSort dataPorts)
open RVSDG (Tuple Wires)
open RVSDG.NestedTheta (Term)
open Join (Opcode model)
open Diamond.Prune (HeaderProjection lowerFlow routeProjectedWith)
open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond (bodyPorts thenBase)
open Nested.Numbered (outerSigs outerArm afterOuterWith routePorts KeptResult)
open Blocks (Bank)
open Blocks.Prune (Mask)

universe u v w

variable {Data : Type u} {Op : SeaOfNodes.Diamond.Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {out : ValueSort Data} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size}
variable (p : Program src entry) {header merge : Mask regs}

/-- Change only the outputs of a region. Child signatures and routes stay
exactly as numbered by the original emitter. -/
def projectResults (mask : Mask regs) {args : List (Ty Data)} :
    {past sigs : List (List (Ty Data))} → Term (Opcode Op) args past sigs (dataPorts regs) →
      Term (Opcode Op) args past sigs (dataPorts mask.kept)
  | _, _, .ret bank => .ret (mask.project bank)
  | _, _, .bind node children rest => .bind node children (projectResults mask rest)

def arm (merge : Mask regs) (i : Fin 2) :
    Term (Opcode Op) (dataPorts regs) [] (outerSigs p i) (dataPorts merge.kept) :=
  projectResults merge (outerArm p i)

abbrev splitSigs (merge : Mask regs) : List (List (Ty Data)) :=
  [routePorts regs, dataPorts merge.kept]

/-- The checked merge consumes only the selected inputs. Fill the other
positions from any in-scope bank when compiling the original quads. -/
def restore {F : Ty Data → Type w} : {regs : List (ValueSort Data)} → (mask : Mask regs) →
    Tuple F (dataPorts regs) → Tuple F (dataPorts mask.kept) → Tuple F (dataPorts regs)
  | _, .nil, .nil, .nil => .nil
  | _, .keep (s := slot) rest, .cons _ old, kept =>
    match (show Tuple F (.value slot :: dataPorts rest.kept) from kept) with
    | .cons field restKept => .cons field (restore rest old restKept)
  | _, .drop rest, .cons dead old, kept => .cons dead (restore rest old kept)

variable (projected : HeaderProjection (src p.header).body header)

/-- The original outer γ now binds only the common kept merge fields. -/
def mergeRegion (merge : Mask regs) : Term (Opcode Op) (dataPorts header.kept) []
    ((src p.header).body.producers ++ splitSigs merge) (dataPorts merge.kept) :=
  thenBase (lowerFlow projected.flow projected.outgoing) fun current =>
    afterOuterWith p (arm p merge) current .ret

/-- Build the smaller γ and emit the original ordered tail. A client must
validate the chosen mask against the observations of this tail. -/
def thetaBodyFor (merge : Mask regs) : Term (Opcode Op) (dataPorts header.kept) []
    ((src p.header).body.producers ++
      (splitSigs merge ++ ((Nested.Numbered.tail p).producers ++ [bodyPorts regs])))
    (bodyPorts header.kept) :=
  thenBase (lowerFlow projected.flow projected.outgoing) fun current =>
    afterOuterWith p (arm p merge) current fun kept =>
      let fallback := current.map fun _ wire =>
        keep (added := dataPorts merge.kept) (keep (added := routePorts regs) wire)
      thenBase ((Nested.Numbered.tail p).lowerFrom (restore merge fallback kept) .jump)
        (routeProjectedWith p.again header)

/-- A complete-bank certificate makes the dropped inputs unobservable. -/
def thetaBody (_checked : Checked p merge) :=
  thetaBodyFor p projected merge

def latchPacket (header : Mask regs) (m : Model.{u, v, w} Op) (final : Bank (regs := regs) m) :=
  RVSDG.Theta.bodyResult (model m) (final.get p.again).down (header.project final)

def lower (checked : Checked p merge) (result : KeptResult p (mask := header)) :=
  Nested.Numbered.lowerWith p result (thetaBody p projected checked)

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Numbered
