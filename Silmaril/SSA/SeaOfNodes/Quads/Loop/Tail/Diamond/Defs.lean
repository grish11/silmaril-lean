module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Chain.Segment.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Join.Finite.Defs
public import Silmaril.SSA.RVSDG.NestedTheta.Defs

/-! # A checked quad loop with one internal diamond -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond

open SeaOfNodes.Diamond (ValueSort Model Ty dataPorts)
open RVSDG (Dialect Port PortType Wires extend)
open RVSDG.NestedTheta (Term)
open Join (Block Opcode)
open Join.Finite (Stage Plan lastBank)
open Blocks (Bank)

universe u v w

variable {Data : Type u} {Op : SeaOfNodes.Diamond.Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {out : ValueSort Data} {size : Nat}

abbrev Source (Op : SeaOfNodes.Diamond.Signature.{u, v} Data)
    (regs : List (ValueSort Data)) (out : ValueSort Data) (size : Nat := 6) :=
  Tail.Source Op regs out size

/-- Two disjoint arm segments run from the header split to the same merge.
One may be a direct edge. The merge jumps to the distinct tested latch. -/
structure Program (src : Source Op regs out size) (entry : Fin size) where
  header : Fin size
  onTrue : Fin size
  onFalse : Fin size
  join : Fin size
  latch : Fin size
  condition : Port (dataPorts regs) (.value .predicate)
  again : Port (dataPorts regs) (.value .predicate)
  result : Port (dataPorts regs) (.value out)
  entryEdge : (src entry).terminator = .transfer (.jump header)
  splitEdge : (src header).terminator = .branch condition (.jump onTrue) (.jump onFalse)
  trueArm : Chain.Segment src join onTrue
  falseArm : Chain.Segment src join onFalse
  armsDistinct : onTrue ≠ onFalse
  joinEdge : (src join).terminator = .transfer (.jump latch)
  latchEdge : (src latch).terminator = .branch again (.jump header) (.ret result)
  distinct : ([entry, header] ++ trueArm.blocks ++ falseArm.blocks ++ [join, latch]).Nodup
  covers : ([entry, header] ++ trueArm.blocks ++ falseArm.blocks ++ [join, latch]).length = size

/-- Discover the merge immediately before the latch on the true route,
then check both linear arms up to that same merge. -/
def check (src : Source Op regs out size) (entry : Fin size) : Option (Program src entry) :=
  match entryEdge : (src entry).terminator with
  | .transfer (.jump header) =>
    match splitEdge : (src header).terminator with
    | .branch condition (.jump onTrue) (.jump onFalse) => do
      let trueRoute ← Chain.findPath src header size onTrue
      let falseRoute ← Chain.findPath src header size onFalse
      match trueRoute.beforeLatch with
      | none => none
      | some join => do
        let trueArm ← trueRoute.segmentTo join
        let falseArm ← falseRoute.segmentTo join
        match joinEdge : (src join).terminator with
        | .transfer (.jump latch) =>
          match latchEdge : (src latch).terminator with
          | .branch again (.jump target) (.ret result) =>
            let order := [entry, header] ++ trueArm.blocks ++ falseArm.blocks ++ [join, latch]
            if shape : target = header ∧ onTrue ≠ onFalse ∧ order.Nodup ∧ order.length = size then
              some ⟨header, onTrue, onFalse, join, latch, condition, again, result, entryEdge,
                splitEdge, trueArm, falseArm, shape.2.1, joinEdge, shape.1 ▸ latchEdge, shape.2.2.1, shape.2.2.2⟩
            else none
          | _ => none
        | _ => none
    | _ => none
  | _ => none

variable {src : Source Op regs out size} {entry : Fin size} (p : Program src entry)

/-- Map each selector occurrence to its original target in the header. -/
def Program.armStart : Fin 2 → Fin size :=
  Fin.cases p.onTrue (fun _ => p.onFalse)

def Program.armPath (occurrence : Fin 2) : Chain.Segment src p.join (p.armStart occurrence) :=
  Fin.cases (motive := fun i => Chain.Segment src p.join (p.armStart i))
    p.trueArm (fun _ => p.falseArm) occurrence

/-- The incoming merge occurrences remain in true/false order. A direct
edge comes from the split header, and a linear arm from its last block. -/
def Program.predecessor (occurrence : Fin 2) : Fin size :=
  (p.armPath occurrence).predecessor p.header

def Program.stage : Stage Op regs :=
  ⟨p.trueArm.quads, p.falseArm.quads, [], .test p.condition (.take 0) (.take 1)⟩

def Program.tail : Block Op regs := (src p.join).body ++ (src p.latch).body

/-- Run the source activation, including the selected arm and both blocks
after reconvergence. The resulting bank supplies feedback or the return. -/
def Program.nextBank (m : Model.{u, v, w} Op) (old : Bank (regs := regs) m) : Bank (regs := regs) m :=
  p.tail.eval m (p.stage.eval m ((src p.header).body.eval m old))

/-- Choose the same occurrence used by the compiled γ, after the header writes. -/
def Program.selected (m : Model.{u, v, w} Op) (old : Bank (regs := regs) m) : Fin 2 :=
  p.stage.choice.eval ((src p.header).body.eval m old)

/-- A header, merge and latch visit accompany every block of the chosen arm. -/
def Program.activationCost (occurrence : Fin 2) : Nat :=
  (p.armPath occurrence).blocks.length + 3

/-- Record one merge occurrence per activation until return or exhaustion. -/
def traceFrom {BankState : Type w} (step : BankState → Fin 2 × Bool × BankState) :
    Nat → BankState → List (Fin 2)
  | 0, _ => []
  | fuel + 1, old =>
    let (occurrence, again, next) := step old
    occurrence :: if again then traceFrom step fuel next else []

/-- Record the selected merge occurrences for the full-bank loop. -/
def Program.trace (m : Model.{u, v, w} Op) : Nat → Bank (regs := regs) m → List (Fin 2) :=
  traceFrom fun old =>
    let next := p.nextBank m old
    (p.selected m old, (next.get p.again).down, next)

/-- Count source visits in a bounded native execution, including the entry. -/
def Program.sourceVisits (m : Model.{u, v, w} Op) (fuel : Nat) (input : Bank (regs := regs) m) : Nat :=
  ((p.trace m fuel ((src entry).body.eval m input)).map p.activationCost).sum + 1

section Prefix

variable {V S : Type u} {Φ : Dialect.{u, v} V S}
variable {args bank outs : List (PortType V S)} {suffix : List (List (PortType V S))}

/-- Use a base RVSDG region as a prefix of a nested one. The continuation
receives its actual result wires in their existing producer scope. -/
def thenBase : {past frontSigs : List (List (PortType V S))} →
    RVSDG.Term Φ args past frontSigs bank →
    (Wires args (extend past frontSigs) bank → Term Φ args (extend past frontSigs) suffix outs) →
    Term Φ args past (frontSigs ++ suffix) outs
  | _, _, .ret wires, next => next wires
  | _, _, .bind node children rest, next =>
    .bind (.ofBase node) (fun i => .ofBase (children i)) (thenBase rest next)

end Prefix

abbrev bodyPorts (regs : List (ValueSort Data)) :=
  RVSDG.Theta.BodyResults (dataPorts regs)

abbrev Program.plan : Plan Op regs := [p.stage]

abbrev Program.bodySigs :=
  (src p.header).body.producers ++ (p.plan.producers ++ (p.tail.producers ++ [bodyPorts regs]))

/-- Use the post-latch test to tag the complete updated bank. -/
def latchNodeFor (again : Port (dataPorts regs) (.value .predicate))
    {args : List (Ty Data)} {past : List (List (Ty Data))}
    (bank : Wires args past (dataPorts regs)) : RVSDG.Node (Opcode Op) args past (bodyPorts regs) :=
  ⟨_, .simple (.route (.test again (.take 1) (.take 0))), bank, Fin.elim0⟩

def Program.latchNode {args : List (Ty Data)} {past : List (List (Ty Data))}
    (bank : Wires args past (dataPorts regs)) : RVSDG.Node (Opcode Op) args past (bodyPorts regs) :=
  latchNodeFor p.again bank

/-- Tag the full carried bank for the next θ activation or for exit. -/
def routeLatchWith {args : List (Ty Data)} {past : List (List (Ty Data))}
    (again : Port (dataPorts regs) (.value .predicate)) (bank : Wires args past (dataPorts regs)) :
    Term (Opcode Op) args past [bodyPorts regs] (bodyPorts regs) :=
  .bind (.ofBase (latchNodeFor again bank)) (fun i => i.elim0) (.ret (lastBank past (bodyPorts regs)))

def Program.routeLatch {past : List (List (Ty Data))}
    (bank : Wires (dataPorts regs) past (dataPorts regs)) :
    Term (Opcode Op) (dataPorts regs) past [bodyPorts regs] (bodyPorts regs) :=
  routeLatchWith p.again bank

/-- Feed the post-header bank to the existing γ compiler, then run the
common merge and latch quads before the supplied tail continuation. -/
def Program.afterHeader {args results : List (Ty Data)} {past suffix : List (List (Ty Data))}
    (current : Wires args past (dataPorts regs))
    (finish : Wires args (extend (extend past p.plan.producers) p.tail.producers) (dataPorts regs) →
      Term (Opcode Op) args (extend (extend past p.plan.producers) p.tail.producers) suffix results) :
    Term (Opcode Op) args past (p.plan.producers ++ (p.tail.producers ++ suffix)) results :=
  thenBase (p.plan.lowerFrom current) fun merged =>
    thenBase (p.tail.lowerFrom merged .jump) finish

/-- The γ result ports are the merge Φs. The merge and latch read the
same selected bank. -/
def Program.thetaBody :
    Term (Opcode Op) (dataPorts regs) [] p.bodySigs (bodyPorts regs) :=
  thenBase ((src p.header).body.lowerFrom (initial regs) .jump) fun current =>
    p.afterHeader current p.routeLatch

/-- Link a full-bank θ body to the result port of its stopping packet. -/
def iterateThenReturnWith {past sigs : List (List (Ty Data))}
    (body : Term (Opcode Op) (dataPorts regs) [] sigs (bodyPorts regs))
    (result : Port (dataPorts regs) (.value out)) (bank : Wires (dataPorts regs) past (dataPorts regs)) :
    Term (Opcode Op) (dataPorts regs) past [dataPorts regs] [.value out] :=
  .bind ⟨_, .theta (dataPorts regs), bank, fun _ => sigs⟩
    (fun _ => body) (.ret (.cons ((lastBank past (dataPorts regs)).get result) .nil))

def Program.iterateThenReturn {past : List (List (Ty Data))}
    (bank : Wires (dataPorts regs) past (dataPorts regs)) :
    Term (Opcode Op) (dataPorts regs) past [dataPorts regs] [.value out] :=
  iterateThenReturnWith p.thetaBody p.result bank

/-- The preheader supplies the entry bank. The numbered θ binds the feedback
bank atomically and returns the result slot of the stopping activation. -/
def Program.lowerTerm :
    Term (Opcode Op) (dataPorts regs) [] ((src entry).body.producers ++ [dataPorts regs]) [.value out] :=
  thenBase ((src entry).body.lowerFrom (initial regs) .jump) p.iterateThenReturn

def Program.lower :
    RVSDG.NestedTheta.Graph (Opcode Op) (dataPorts regs) []
      ((src entry).body.producers ++ [dataPorts regs]) [.value out] :=
  p.lowerTerm.toGraph

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond
