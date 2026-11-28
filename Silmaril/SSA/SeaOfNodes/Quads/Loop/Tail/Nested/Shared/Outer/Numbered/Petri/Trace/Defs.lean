module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Boundaries.Defs

/-! # Ordered join packets in the original numbered θ execution -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri

open SeaOfNodes.Diamond (ValueSort)
open SeaOfNodes.Loop.MLIR.CF (Op model)
open Silmaril.MLIR.Arith (Width Env)
open SeaOfNodes.MLIR.Lowering (encodeValues)
open Diamond.MLIR.CF (Widths)
open Blocks (Bank)
open RVSDG.NestedTheta.Petri (Fire Marking finished pending)
open RVSDG.NestedTheta (Term)
open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond (iterateThenReturnWith)
open Shared.Numbered.Execution (lowerTerm)
open Shared.MLIR.CF.InnerPhi (headerBank side occurrence)
open Relation (ReflTransGen)

variable {regs : List (ValueSort Width)} {out : ValueSort Width} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size} (p : Program src entry)

structure Packets (regs : List (ValueSort Width)) (size : Nat) where
  inner : Option ((Fin size × Fin 2) × Bank (regs := regs) model)
  outer : (Fin size × Fin 2) × Bank (regs := regs) model

def packetsAt (old : Bank (regs := regs) model) : Packets regs size where
  inner := if (headerBank p.toRoutes old |>.get p.outerTest).down then
    some (p.toRoutes.innerEdgeOccurrence (side p.toRoutes old),
      p.toRoutes.prefixBank model old (occurrence (side p.toRoutes old)))
    else none
  outer := (p.outerEdgeOccurrence (MLIR.CF.Phi.arrivalSide (p := p) old),
    p.outerBank model old (p.toControl.selected model old))

abbrev CFPackets (regs : List (ValueSort Width)) (size : Nat) :=
  Option ((Fin size × Fin 2) × Env (Widths regs)) × ((Fin size × Fin 2) × Env (Widths regs))

def Packets.encode (packets : Packets regs size) : CFPackets regs size :=
  (packets.inner.map (fun (edge, bank) => (edge, encodeValues bank)),
    (packets.outer.1, encodeValues packets.outer.2))

/-- Evaluate the selected scoped operands read back from the actual CF
terminators through Φ, in their destination order. -/
def cfPacketsAt (inner : Shared.MLIR.CF.InnerPhi.Rows p.toRoutes) (outer : MLIR.CF.Phi.Rows p)
    (input old : Bank (regs := regs) model) : CFPackets regs size :=
  (if ((headerBank p.toRoutes old).get p.outerTest).down then
    some (p.toRoutes.innerEdgeOccurrence (side p.toRoutes old), inner.bank (side p.toRoutes old) input old)
    else none,
    (p.outerEdgeOccurrence (MLIR.CF.Phi.arrivalSide (p := p) old),
      MLIR.CF.Phi.Readback.readBank outer (MLIR.CF.Phi.arrivalSide (p := p) old)
        (MLIR.CF.Phi.arrivalEnv input old)))

/-- The live outer child at the inner observation. Its true arm can expose
the inner output, and its false arm is explicitly tagged as a bypass. -/
def innerCheckpoint (old : Bank (regs := regs) model)
    (header : Marking semantics (.ofBase (headerCode p)))
    (arm : Fin 2) (child : Marking semantics (Prefix.outerArm p.toRoutes arm)) :
    Marking semantics (thetaBody p) :=
  (outerCut p).2.2.attach semantics
    ((baseCut (headerCode p) (fun wires => Prefix.afterOuter p.toRoutes wires .ret)).attach
      semantics header (.done (taggedHeader p old arm), .waiting arm (headerBank p.toRoutes old, child), PUnit.unit))
    (pending semantics (outerCut p).2.1)

/-- All three segments share the same body markings. The first checkpoint
is inside the live outer child, the second is after the outer γ commits,
and the final marking publishes the complete θ latch packet. -/
structure Activation (old : Bank (regs := regs) model) (packets : Packets regs size)
    (again : Bool) (next : Bank (regs := regs) model) where
  header : Marking semantics (.ofBase (headerCode p))
  arm : Fin 2
  child : Marking semantics (Prefix.outerArm p.toRoutes arm)
  outer : Marking semantics (thetaBody p)
  final : Marking semantics (thetaBody p)
  selected : (Prefix.outerChoice p.toRoutes).eval (headerBank p.toRoutes old) = arm
  entered : ReflTransGen (Fire semantics (thetaBody p) old PUnit.unit) (pending semantics (thetaBody p))
    (innerCheckpoint p old header arm child)
  innerObserved : (readInner p old arm child).map (fun bank =>
    (p.toRoutes.innerEdgeOccurrence (side p.toRoutes old), bank)) = packets.inner
  joined : ReflTransGen (Fire semantics (thetaBody p) old PUnit.unit)
    (innerCheckpoint p old header arm child) outer
  outerObserved : (finished semantics (outerRegion p) old PUnit.unit ((outerCut p).2.2.observe semantics outer)).map
    (fun bank => (p.outerEdgeOccurrence (MLIR.CF.Phi.arrivalSide (p := p) old), bank)) = some packets.outer
  continued : ReflTransGen (Fire semantics (thetaBody p) old PUnit.unit) outer final
  latched : finished semantics (thetaBody p) old PUnit.unit final =
    some (RVSDG.Theta.bodyResult semantics again next)

/-- A stopping activation or a feedback activation followed by more
windows. The feedback bank of each window is the input of the next one. -/
inductive Windows :
    Bank (regs := regs) model → List (Packets regs size) → Bank (regs := regs) model → Type where
  | stop {old final : Bank (regs := regs) model}
      (window : Activation p old (packetsAt p old) false final) :
      Windows old [packetsAt p old] final
  | again {old next final : Bank (regs := regs) model} {packetsLater : List (Packets regs size)}
      (window : Activation p old (packetsAt p old) true next) (rest : Windows next packetsLater final) :
      Windows old (packetsAt p old :: packetsLater) final

def entryCode := (src entry).body.lowerFrom (initial regs) .jump

def entryCut :=
  baseCut (entryCode (src := src) (entry := entry)) (iterateThenReturnWith (thetaBody p) p.result)

abbrev emitted := lowerTerm p.toControl (thetaBody p)

/-- A rooted checkpoint in the actual θ vertex, with the original
preheader marked and the current θ child still resident. -/
def atBody (preheader : Marking semantics (.ofBase (entryCode (src := src) (entry := entry))))
    (old : Bank (regs := regs) model) (mark : Marking semantics (thetaBody p)) :
    Marking semantics (emitted p) :=
  (entryCut p).attach semantics preheader (.waiting (0 : Fin 1) (old, mark), PUnit.unit)

/-- Each listed marking is an endpoint of one firing segment and the
start of the next. All segments use the same original step relation. -/
inductive Visits {M : Type} (step : M → M → Prop) : M → List M → M → Prop where
  | finish {start last : M} (steps : ReflTransGen step start last) : Visits step start [] last
  | visit {start mark last : M} {rest : List M} (steps : ReflTransGen step start mark)
      (remaining : Visits step mark rest last) : Visits step start (mark :: rest) last

/-- The two join observations per activation, in order. At the first
marking the false outer arm records bypass via its waiting tag. -/
def Windows.checkpoints {old packets final} (windows : Windows p old packets final)
    (preheader : Marking semantics (.ofBase (entryCode (src := src) (entry := entry)))) :
    List (Marking semantics (emitted p)) :=
  match windows with
  | .stop window =>
    [atBody p preheader old (innerCheckpoint p old window.header window.arm window.child),
      atBody p preheader old window.outer]
  | .again window rest =>
    atBody p preheader old (innerCheckpoint p old window.header window.arm window.child) ::
      atBody p preheader old window.outer :: checkpoints rest preheader

/-- Original header banks of the observed activations, in the order
in which θ starts from them. -/
def Windows.inputs {old packets final} (windows : Windows p old packets final) :
    List (Bank (regs := regs) model) :=
  match windows with
  | .stop _ => [old]
  | .again _ rest => old :: inputs rest

/-- The checkpoint list and packet list arise from the same windows.
The marking after the last segment decodes the final bank's result. -/
structure Trace (input : Bank (regs := regs) model) (packets : List (Packets regs size))
    (finalBank : Bank (regs := regs) model) where
  preheader : Marking semantics (.ofBase (entryCode (src := src) (entry := entry)))
  windows : Windows p ((src entry).body.eval model input) packets finalBank
  final : Marking semantics (emitted p)
  visits : Visits (Fire semantics (emitted p) input PUnit.unit) (pending semantics (emitted p))
    (Windows.checkpoints p windows preheader) final
  result : finished semantics (emitted p) input PUnit.unit final = some (.cons (finalBank.get p.result) .nil)

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri
