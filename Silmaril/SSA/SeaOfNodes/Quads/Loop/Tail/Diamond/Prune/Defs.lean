module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Blocks.Prune.Defs

/-! # Prune the θ interface of a checked quad diamond -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.Prune

open SeaOfNodes.Diamond (Dataflow Model Ty Val ValueSort dataPorts)
open RVSDG (Port Tuple Wires extend)
open RVSDG.NestedTheta (Term)
open Join (Block Opcode)
open Join.Finite (lastBank)
open Blocks (Bank)
open Blocks.Prune (Mask readSchedule renameFlow renameWires)

universe u v w

variable {Data : Type u} {Op : SeaOfNodes.Diamond.Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {out : ValueSort Data} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size}
def headerTransferFor (body : Block Op regs) :=
  CFG.compileBlock body (initial regs)

/-- Keep the inputs needed to reconstruct the outgoing bank and any
separately retained positions. This analysis retains every producer. -/
def boundaryMaskFor (body : Block Op regs) (keep : Nat → Bool) : Mask regs :=
  let flow := headerTransferFor body
  let reads := readSchedule flow.flow ++ [flow.outgoing.addresses]
  let live := RVSDG.NestedTheta.Liveness.sweep reads 0
  Mask.ofSlots (fun i => keep i || live.contains (.arg i)) regs

/-- A numbered θ also needs its result slot in the stopping packet. -/
def carriedMaskFor (body : Block Op regs) (result : Port (dataPorts regs) (.value out)) : Mask regs :=
  boundaryMaskFor body (fun i => i == result.index)

/-- A strictly smaller bank can reconstruct the whole post-header bank. -/
structure HeaderProjection (body : Block Op regs) (mask : Mask regs) where
  flow : Dataflow Op (dataPorts mask.kept) [] body.producers
  outgoing : Wires (dataPorts mask.kept) (extend [] body.producers) (dataPorts regs)
  smaller : mask.kept.length < regs.length
  flow_eq : renameFlow mask.rename (headerTransferFor body).flow = some flow
  outgoing_eq : renameWires mask.rename (headerTransferFor body).outgoing = some outgoing

def checkHeader (body : Block Op regs) (mask : Mask regs) : Option (HeaderProjection body mask) :=
  if smaller : mask.kept.length < regs.length then
    match flow_eq : renameFlow mask.rename (headerTransferFor body).flow,
          outgoing_eq : renameWires mask.rename (headerTransferFor body).outgoing with
    | some flow, some outgoing => some ⟨flow, outgoing, smaller, flow_eq, outgoing_eq⟩
    | _, _ => none
  else none

def HeaderProjection.headerBank {body : Block Op regs} {mask : Mask regs}
    (projected : HeaderProjection body mask) (m : Model.{u, v, w} Op)
    (old : Bank (regs := mask.kept) m) : Bank (regs := regs) m :=
  projected.outgoing.read old (projected.flow.eval m old PUnit.unit)

variable (p : Program src entry)

def headerTransfer := headerTransferFor (src p.header).body

def carriedMask : Mask regs := carriedMaskFor (src p.header).body p.result

/-- A numbered θ must also carry the return slot in its stop packet. -/
structure Checked (p : Program src entry) (mask : Mask regs)
    extends HeaderProjection (src p.header).body mask where
  result : Port (dataPorts mask.kept) (.value out)
  result_eq : mask.rename p.result = some result

def checkMask (mask : Mask regs) : Option (Checked p mask) := do
  let projected ← checkHeader (src p.header).body mask
  match result_eq : mask.rename p.result with
  | some result => some ⟨projected, result, result_eq⟩
  | none => none

def prune : Option (Checked p (carriedMask p)) := checkMask p (carriedMask p)

variable {p} {mask : Mask regs} (checked : Checked p mask)

def Checked.headerBank (m : Model.{u, v, w} Op) (old : Bank (regs := mask.kept) m) :
    Bank (regs := regs) m :=
  checked.toHeaderProjection.headerBank m old

/-- Use the same trace observer and source arm order as the full bank. -/
def Checked.trace (m : Model.{u, v, w} Op) : Nat → Bank (regs := mask.kept) m → List (Fin 2) :=
  traceFrom fun old =>
    let header := checked.headerBank m old
    let next := p.tail.eval m (p.stage.eval m header)
    (p.stage.choice.eval header, (next.get p.again).down, mask.project next)

/-- Emit the validated producer table as an ordinary base RVSDG prefix. -/
def lowerFlow {args results : List (Ty Data)} :
    {past sigs : List (List (Ty Data))} → Dataflow Op args past sigs →
    Wires args (extend past sigs) results → RVSDG.Term (Opcode Op) args past sigs results
  | _, _, .nil, result => .ret result
  | _, _, .cons op operands rest, result =>
    .bind ⟨_, .simple (.pure op), operands, Fin.elim0⟩ (fun i => i.elim0) (lowerFlow rest result)

def projectPacket (mask : Mask regs) {F : Ty Data → Type w} :
    Tuple F (bodyPorts regs) → Tuple F (bodyPorts mask.kept)
  | .cons tag bank => .cons tag (mask.project bank)

def routeProjectedWith (again : Port (dataPorts regs) (.value .predicate)) (mask : Mask regs)
    {args : List (Ty Data)} {past : List (List (Ty Data))} (bank : Wires args past (dataPorts regs)) :
    Term (Opcode Op) args past [bodyPorts regs] (bodyPorts mask.kept) :=
  .bind (.ofBase (latchNodeFor again bank)) (fun i => i.elim0)
    (.ret (projectPacket mask (lastBank past (bodyPorts regs))))

def routeProjected (p : Program src entry) (mask : Mask regs) {args : List (Ty Data)}
    {past : List (List (Ty Data))} (bank : Wires args past (dataPorts regs)) :
    Term (Opcode Op) args past [bodyPorts regs] (bodyPorts mask.kept) :=
  routeProjectedWith p.again mask bank

/-- The smaller θ argument bank is expanded by the header producers.
The γ regions and their selected merge column are reused verbatim. -/
def Checked.thetaBody :
    Term (Opcode Op) (dataPorts mask.kept) [] p.bodySigs (bodyPorts mask.kept) :=
  thenBase (lowerFlow checked.flow checked.outgoing) fun current =>
    p.afterHeader current (routeProjected p mask)

/-- Bind the projected entry and feedback bank in θ and read the retained
return slot of the stopping activation. -/
def thetaThenReturn (mask : Mask regs) {sigs : List (List (Ty Data))} {past : List (List (Ty Data))}
    (body : Term (Opcode Op) (dataPorts mask.kept) [] sigs (bodyPorts mask.kept))
    (result : Port (dataPorts mask.kept) (.value out)) (bank : Wires (dataPorts regs) past (dataPorts regs)) :
    Term (Opcode Op) (dataPorts regs) past [dataPorts mask.kept] [.value out] :=
  .bind ⟨_, .theta (dataPorts mask.kept), mask.project bank, fun _ => sigs⟩
    (fun _ => body) (.ret (.cons ((lastBank past (dataPorts mask.kept)).get result) .nil))

def Checked.iterateThenReturn {past : List (List (Ty Data))}
    (bank : Wires (dataPorts regs) past (dataPorts regs)) :
    Term (Opcode Op) (dataPorts regs) past [dataPorts mask.kept] [.value out] :=
  thetaThenReturn mask checked.thetaBody checked.result bank

def Checked.lowerTerm :
    Term (Opcode Op) (dataPorts regs) [] ((src entry).body.producers ++ [dataPorts mask.kept]) [.value out] :=
  thenBase ((src entry).body.lowerFrom (initial regs) .jump) checked.iterateThenReturn

def Checked.lower :
    RVSDG.NestedTheta.Graph (Opcode Op) (dataPorts regs) []
      ((src entry).body.producers ++ [dataPorts mask.kept]) [.value out] :=
  checked.lowerTerm.toGraph

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.Prune
