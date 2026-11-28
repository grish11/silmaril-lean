module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Numbered.Defs

/-! # Numbered γ/θ with a shared continuation inside the outer true arm -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Numbered

open SeaOfNodes.Diamond (Model Ty ValueSort dataPorts)
open RVSDG (Wires extend)
open RVSDG.NestedTheta (Term)
open Join (Block Choice Opcode)
open Join.Finite (Plan)
open Nested.Numbered (linkGamma splitSigs)
open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond (bodyPorts thenBase routeLatchWith iterateThenReturnWith)
open Blocks (Bank)

universe u v w

variable {Data : Type u} {Op : SeaOfNodes.Diamond.Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {out : ValueSort Data} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size} (p : Program src entry)

def innerPlan : Plan Op regs :=
  [⟨p.innerTrue.quads, p.innerFalse.quads, [], .test p.innerTest (.take 0) (.take 1)⟩]

abbrev innerSigs :=
  (src p.inner).body.producers ++ ((innerPlan p).producers ++ p.suffix.quads.producers)

/-- Only the prefixes are γ children. The suffix reads the chosen γ
result wires in the enclosing outer-true region. -/
def innerRegion : Term (Opcode Op) (dataPorts regs) [] (innerSigs p) (dataPorts regs) :=
  thenBase ((src p.inner).body.lowerFrom (initial regs) .jump) fun current =>
    thenBase ((innerPlan p).lowerFrom current) fun incoming =>
      .ofBase (p.suffix.quads.lowerFrom incoming .jump)

def outerChoice : Choice regs 2 :=
  .test p.outerTest (.take 0) (.take 1)

def outerSigs : Fin 2 → List (List (Ty Data)) :=
  Fin.cases (innerSigs p) (fun _ => p.outerFalse.quads.producers)

def outerArm (i : Fin 2) : Term (Opcode Op) (dataPorts regs) [] (outerSigs p i) (dataPorts regs) :=
  Fin.cases (motive := fun i => Term (Opcode Op) (dataPorts regs) [] (outerSigs p i) (dataPorts regs))
    (innerRegion p) (fun _ => .ofBase (p.outerFalse.quads.lowerFrom (initial regs) .jump)) i

def afterOuter {args results : List (Ty Data)} {past suffix : List (List (Ty Data))}
    (current : Wires args past (dataPorts regs))
    (finish : Wires args (extend past (splitSigs regs)) (dataPorts regs) →
      Term (Opcode Op) args (extend past (splitSigs regs)) suffix results) :
    Term (Opcode Op) args past (splitSigs regs ++ suffix) results :=
  linkGamma (outerChoice p) (outerSigs p) (outerArm p) current finish

/-- Expose the emitted region through the original common merge boundary. -/
def mergeRegion : Term (Opcode Op) (dataPorts regs) []
    ((src p.header).body.producers ++ splitSigs regs) (dataPorts regs) :=
  thenBase ((src p.header).body.lowerFrom (initial regs) .jump) fun current =>
    afterOuter p current .ret

def tail : Block Op regs := (src p.join).body ++ (src p.latch).body

def nextBank (m : Model.{u, v, w} Op) (old : Bank (regs := regs) m) : Bank (regs := regs) m :=
  (tail p).eval m (p.mergeBank m old (p.toControl.selected m old))

def activationCost (m : Model.{u, v, w} Op) (old : Bank (regs := regs) m) : Nat :=
  p.mergeVisits (p.toControl.selected m old) + 2

/-- Count original block visits on the chosen routes, stopping at an exit. -/
def visitsFrom (m : Model.{u, v, w} Op) : Nat → Bank (regs := regs) m → Nat
  | 0, _ => 0
  | fuel + 1, old =>
    let next := nextBank p m old
    (if (next.get p.again).down then visitsFrom m fuel next else 0) + activationCost p m old

def sourceVisits (m : Model.{u, v, w} Op) (fuel : Nat) (input : Bank (regs := regs) m) : Nat :=
  visitsFrom p m fuel ((src entry).body.eval m input) + 1

abbrev bodySigs :=
  (src p.header).body.producers ++ (splitSigs regs ++ ((tail p).producers ++ [bodyPorts regs]))

def thetaBody : Term (Opcode Op) (dataPorts regs) [] (bodySigs p) (bodyPorts regs) :=
  thenBase ((src p.header).body.lowerFrom (initial regs) .jump) fun current =>
    afterOuter p current fun merged =>
      thenBase ((tail p).lowerFrom merged .jump) (routeLatchWith p.again)

def lowerTerm :
    Term (Opcode Op) (dataPorts regs) [] ((src entry).body.producers ++ [dataPorts regs]) [.value out] :=
  thenBase ((src entry).body.lowerFrom (initial regs) .jump) (iterateThenReturnWith (thetaBody p) p.result)

def lower : RVSDG.NestedTheta.Graph (Opcode Op) (dataPorts regs) []
    ((src entry).body.producers ++ [dataPorts regs]) [.value out] :=
  (lowerTerm p).toGraph

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Numbered
