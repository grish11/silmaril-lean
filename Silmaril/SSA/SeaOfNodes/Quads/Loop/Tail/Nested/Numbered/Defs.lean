module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.Prune.Defs

/-! # Numbered γ/θ lowering of the checked three-occurrence quad loop -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Numbered

open SeaOfNodes.Diamond (Model Ty ValueSort dataPorts)
open RVSDG (Port Wires extend)
open RVSDG.NestedTheta (Term)
open Join (Block Choice Opcode)
open Join.Finite (Plan lastBank)
open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond (bodyPorts thenBase)
open Diamond.Prune (HeaderProjection lowerFlow routeProjectedWith thetaThenReturn)
open Blocks (Bank)
open Blocks.Prune (Mask)

universe u v w

variable {Data : Type u} {Op : SeaOfNodes.Diamond.Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {out : ValueSort Data} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size}
variable (p : Program src entry)

def innerPlan : Plan Op regs :=
  [⟨p.innerTrue.quads, p.innerFalse.quads, [], .test p.innerTest (.take 0) (.take 1)⟩]

/-- Execute the inner split's writes inside the outer true arm. Even when
one inner arm is empty, that arm sees the latest post-inner definitions. -/
def innerRegion : Term (Opcode Op) (dataPorts regs) []
    ((src p.inner).body.producers ++ (innerPlan p).producers) (dataPorts regs) :=
  thenBase ((src p.inner).body.lowerFrom (initial regs) .jump) fun current =>
    thenBase ((innerPlan p).lowerFrom current) .ret

def outerChoice : Choice regs 2 :=
  .test p.outerTest (.take 0) (.take 1)

def outerSigs : Fin 2 → List (List (Ty Data)) :=
  Fin.cases ((src p.inner).body.producers ++ (innerPlan p).producers)
    (fun _ => p.outerFalse.quads.producers)

def outerArm (i : Fin 2) : Term (Opcode Op) (dataPorts regs) [] (outerSigs p i) (dataPorts regs) :=
  Fin.cases (motive := fun i => Term (Opcode Op) (dataPorts regs) [] (outerSigs p i) (dataPorts regs))
    (innerRegion p) (fun _ => .ofBase (p.outerFalse.quads.lowerFrom (initial regs) .jump)) i

abbrev routePorts (regs : List (ValueSort Data)) : List (Ty Data) :=
  .control 2 :: dataPorts regs

abbrev splitSigs (regs : List (ValueSort Data)) : List (List (Ty Data)) :=
  [routePorts regs, dataPorts regs]

/-- Link a two-arm γ to a continuation over the actual numbered result
ports. Each isolated child has the same typed result interface. -/
def linkGamma {args outputs results : List (Ty Data)} {past suffix : List (List (Ty Data))}
    (choice : Choice regs 2) (sigs : Fin 2 → List (List (Ty Data)))
    (arms : (i : Fin 2) → Term (Opcode Op) (dataPorts regs) [] (sigs i) outputs)
    (current : Wires args past (dataPorts regs))
    (finish : Wires args (extend past [routePorts regs, outputs]) outputs →
      Term (Opcode Op) args (extend past [routePorts regs, outputs]) suffix results) :
    Term (Opcode Op) args past ([routePorts regs, outputs] ++ suffix) results :=
  .bind ⟨_, .base (.simple (.route choice)), current, Fin.elim0⟩ (fun i => i.elim0)
    (.bind ⟨_, .base (.gamma 0), lastBank past (routePorts regs), sigs⟩
      arms (finish (lastBank (past ++ [routePorts regs]) outputs)))

/-- Wire the outer γ with the supplied common result interface. Each arm
must already return that interface in the same port order. -/
def afterOuterWith {args outputs results : List (Ty Data)} {past suffix : List (List (Ty Data))}
    (arms : (i : Fin 2) → Term (Opcode Op) (dataPorts regs) [] (outerSigs p i) outputs)
    (current : Wires args past (dataPorts regs))
    (finish : Wires args (extend past [routePorts regs, outputs]) outputs →
      Term (Opcode Op) args (extend past [routePorts regs, outputs]) suffix results) :
    Term (Opcode Op) args past ([routePorts regs, outputs] ++ suffix) results :=
  linkGamma (outerChoice p) (outerSigs p) arms current finish

/-- The outer γ returns the complete bank from its chosen region. -/
def afterOuter {args results : List (Ty Data)} {past suffix : List (List (Ty Data))}
    (current : Wires args past (dataPorts regs))
    (finish : Wires args (extend past (splitSigs regs)) (dataPorts regs) →
      Term (Opcode Op) args (extend past (splitSigs regs)) suffix results) :
    Term (Opcode Op) args past (splitSigs regs ++ suffix) results :=
  afterOuterWith p (outerArm p) current finish

/-- Source bank delivered by the selected γ region after the header. -/
def branchBank (m : Model.{u, v, w} Op) (header : Bank (regs := regs) m) :=
  if (header.get p.outerTest).down then
    (innerPlan p).eval m ((src p.inner).body.eval m header)
  else p.outerFalse.quads.eval m header

def tail : Block Op regs := (src p.join).body ++ (src p.latch).body

def nextBank (m : Model.{u, v, w} Op) (old : Bank (regs := regs) m) : Bank (regs := regs) m :=
  (tail p).eval m (p.mergeBank m old (p.selected m old))

/-- Source visits spent by a native activation bound, including early stop. -/
def visitsFrom (m : Model.{u, v, w} Op) : Nat → Bank (regs := regs) m → Nat
  | 0, _ => 0
  | fuel + 1, old =>
    let next := nextBank p m old
    (if (next.get p.again).down then visitsFrom m fuel next else 0) +
      (p.mergeVisits (p.selected m old) + 2)

def sourceVisits (m : Model.{u, v, w} Op) (fuel : Nat) (input : Bank (regs := regs) m) : Nat :=
  visitsFrom p m fuel ((src entry).body.eval m input) + 1

variable {mask : Mask regs} (projected : HeaderProjection (src p.header).body mask)

/-- Expose the actual region from the projected header to the common merge. -/
def mergeRegion : Term (Opcode Op) (dataPorts mask.kept) []
    ((src p.header).body.producers ++ splitSigs regs) (dataPorts regs) :=
  thenBase (lowerFlow projected.flow projected.outgoing) fun current =>
    afterOuter p current .ret

def thetaBody : Term (Opcode Op) (dataPorts mask.kept) []
    ((src p.header).body.producers ++ (splitSigs regs ++ ((tail p).producers ++ [bodyPorts regs])))
    (bodyPorts mask.kept) :=
  thenBase (lowerFlow projected.flow projected.outgoing) fun current =>
    afterOuter p current fun merged =>
      thenBase ((tail p).lowerFrom merged .jump) (routeProjectedWith p.again mask)

/-- A numbered θ yields only carried fields. Check that the shared header
projection retained the source return slot before emitting the loop. -/
abbrev KeptResult :=
  {result : Port (dataPorts mask.kept) (.value out) // mask.rename p.result = some result}

def checkResult (mask : Mask regs) : Option (KeptResult p (mask := mask)) :=
  match renamed : mask.rename p.result with
  | some result => some ⟨result, renamed⟩
  | none => none

def lowerTermWith (result : KeptResult p (mask := mask)) {sigs : List (List (Ty Data))}
    (body : Term (Opcode Op) (dataPorts mask.kept) [] sigs (bodyPorts mask.kept)) :
    Term (Opcode Op) (dataPorts regs) [] ((src entry).body.producers ++ [dataPorts mask.kept]) [.value out] :=
  thenBase ((src entry).body.lowerFrom (initial regs) .jump) (thetaThenReturn mask body result.val)

def lowerWith (result : KeptResult p (mask := mask)) {sigs : List (List (Ty Data))}
    (body : Term (Opcode Op) (dataPorts mask.kept) [] sigs (bodyPorts mask.kept)) :
    RVSDG.NestedTheta.Graph (Opcode Op) (dataPorts regs) []
      ((src entry).body.producers ++ [dataPorts mask.kept]) [.value out] :=
  (lowerTermWith p result body).toGraph

def lowerTerm (result : KeptResult p (mask := mask)) :
    Term (Opcode Op) (dataPorts regs) [] ((src entry).body.producers ++ [dataPorts mask.kept]) [.value out] :=
  lowerTermWith p result (thetaBody p projected)

def lower (result : KeptResult p (mask := mask)) :
    RVSDG.NestedTheta.Graph (Opcode Op) (dataPorts regs) []
      ((src entry).body.producers ++ [dataPorts mask.kept]) [.value out] :=
  lowerWith p result (thetaBody p projected)

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Numbered
