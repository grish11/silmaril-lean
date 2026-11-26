module

public import Silmaril.SSA.RVSDG.NestedTheta.Petri.Cut.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.MLIR.CF.InnerPhi.Defs

/-! # Typed cuts at the two emitted γ result banks -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri

open SeaOfNodes.Diamond (Ty ValueSort dataPorts)
open SeaOfNodes.Loop.MLIR.CF (Op model)
open Silmaril.MLIR.Arith (Width)
open Join (Opcode)
open Blocks (Bank)
open RVSDG (Tuple Wires extend)
open RVSDG.NestedTheta (Term)
open RVSDG.NestedTheta.Petri (Cut Fire Marking finished pending)
open Relation (ReflTransGen)
open Shared.MLIR.CF.InnerPhi (afterInner headerBank)
open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond (thenBase routeLatchWith)
open Nested.Numbered (routePorts)
open Join.Finite (lastBank)

universe u v

section Prefix
variable {V S : Type u} {Φ : RVSDG.Dialect.{u, v} V S}
variable {args mid bank outs : List (RVSDG.PortType V S)}
variable {past prefixSigs wholeSigs : List (List (RVSDG.PortType V S))}

abbrev Cursor (front : Term Φ args past prefixSigs bank) (whole : Term Φ args past wholeSigs outs) :=
  (tailSigs : List (List (RVSDG.PortType V S))) ×
    (tail : Term Φ args (extend past prefixSigs) tailSigs outs) × Cut front whole tail

/-- Pass a cut through exactly the common emitted base bindings. -/
def throughBase :
    {past sigs : List (List (RVSDG.PortType V S))} →
    (base : RVSDG.Term Φ args past sigs mid) →
    (front : Wires args (extend past sigs) mid → Term Φ args (extend past sigs) prefixSigs bank) →
    (whole : Wires args (extend past sigs) mid → Term Φ args (extend past sigs) wholeSigs outs) →
    (∀ wires, Cursor (front wires) (whole wires)) →
      Cursor (thenBase base front) (thenBase base whole)
  | _, _, .ret wires, _, _, cut => cut wires
  | _, _, .bind node children rest, front, whole, cut =>
    let ⟨sigs, tail, next⟩ := @throughBase _ _ rest front whole cut
    ⟨sigs, tail, .bind (.ofBase node) (fun i => .ofBase (children i)) next⟩

/-- The actual result wires of a base spine before its continuation. -/
def endWires : {past sigs : List (List (RVSDG.PortType V S))} →
    RVSDG.Term Φ args past sigs mid → Wires args (extend past sigs) mid
  | _, _, .ret wires => wires
  | _, _, @RVSDG.Term.bind _ _ _ _ head _ past sigs _ _ rest => @endWires (past ++ [head]) sigs rest

/-- Keep the post-prefix term itself as the index of the cut. -/
def baseCut : {past sigs : List (List (RVSDG.PortType V S))} →
    (base : RVSDG.Term Φ args past sigs mid) →
    (finish : Wires args (extend past sigs) mid → Term Φ args (extend past sigs) wholeSigs outs) →
    Cut (.ofBase base) (thenBase base finish) (finish (endWires base))
  | _, _, .ret wires, finish => .stop wires (finish wires)
  | _, _, .bind node children rest, finish =>
    .bind (.ofBase node) (fun i => .ofBase (children i)) (@baseCut _ _ rest finish)

end Prefix

variable {regs : List (ValueSort Width)} {out : ValueSort Width} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size} (p : Program src entry)

abbrev semantics := Join.model model

def innerPrefix := afterInner p.toRoutes .ret

def innerCut : Cursor (innerPrefix p) (Prefix.innerRegion p.toRoutes) :=
  throughBase ((src p.inner).body.lowerFrom (initial regs) .jump) _ _ fun current =>
    throughBase ((Prefix.innerPlan p.toRoutes).lowerFrom current) .ret
      (fun incoming => .ofBase (p.suffix.quads.lowerFrom incoming .jump))
      (fun incoming => ⟨_, _, .stop incoming _⟩)

def outerContinuation
    (bank : Wires (dataPorts regs) (outerScope p) (dataPorts regs)) :=
  thenBase (p.outerSuffix.quads.lowerFrom bank .jump) fun merged =>
    thenBase ((tail p).lowerFrom merged .jump) (routeLatchWith p.again)

def headerCode := (src p.header).body.lowerFrom (initial regs) .jump

def afterHeader
    (bank : Wires (dataPorts regs) (extend [] (src p.header).body.producers) (dataPorts regs)) :=
  Prefix.afterOuter p.toRoutes bank (outerContinuation p)

def headerCut : Cut (.ofBase (headerCode p)) (thetaBody p) (afterHeader p (endWires (headerCode p))) :=
  baseCut (headerCode p) (afterHeader p)

def outerCut : Cursor (outerRegion p) (thetaBody p) :=
  throughBase (headerCode p) (fun current => Prefix.afterOuter p.toRoutes current .ret)
    (afterHeader p) fun _ => ⟨_, _, .bind _ _ (.bind _ _ (.stop _ _))⟩

/-- Observe the complete bank produced by the outer γ inside the θ body. -/
def OuterReads (old bank : Bank (regs := regs) model) : Prop :=
  (outerCut p).2.2.Reads semantics old bank

/-- Observe the complete bank produced by the inner γ inside the original
outer-true child. The child's own argument tuple is the post-header bank. -/
def InnerReads (old bank : Bank (regs := regs) model) : Prop :=
  (innerCut p).2.2.Reads semantics (headerBank p.toRoutes old) bank

/-- Read the inner boundary while the actual outer γ retains its live
child. The false child bypasses the inner γ. -/
def readInner (old : Bank (regs := regs) model) :
    (arm : Fin 2) → Marking semantics (Prefix.outerArm p.toRoutes arm) → Option (Bank (regs := regs) model) :=
  Fin.cases (motive := fun arm => Marking semantics (Prefix.outerArm p.toRoutes arm) → Option (Bank (regs := regs) model))
    (fun mark => finished semantics (innerPrefix p) (headerBank p.toRoutes old) PUnit.unit
      ((innerCut p).2.2.observe semantics mark))
    (fun _ _ => none)

def taggedHeader (old : Bank (regs := regs) model) (arm : Fin 2) :
    Tuple semantics.Val (routePorts regs) :=
  .cons ⟨arm⟩ (headerBank p.toRoutes old)

def waitingMark (old : Bank (regs := regs) model) (arm : Fin 2)
    (child : Marking semantics (Prefix.outerArm p.toRoutes arm)) :
    Marking semantics (afterHeader p (endWires (headerCode p))) :=
  (.done (taggedHeader p old arm), .waiting arm (headerBank p.toRoutes old, child),
    pending semantics (outerContinuation p (lastBank _ _)))

/-- The actual θ body can reach the live selected outer γ child with this mark. -/
def Waiting (old : Bank (regs := regs) model) (arm : Fin 2)
    (child : Marking semantics (Prefix.outerArm p.toRoutes arm)) : Prop :=
  ∃ headerMark, ReflTransGen (Fire semantics (thetaBody p) old PUnit.unit) (pending semantics (thetaBody p))
    ((headerCut p).attach semantics headerMark (waitingMark p old arm child))

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri
