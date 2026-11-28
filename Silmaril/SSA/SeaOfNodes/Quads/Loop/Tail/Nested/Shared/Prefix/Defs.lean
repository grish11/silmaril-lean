module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Numbered.Defs

/-! # Typed routing to either profile’s outer merge boundary -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Prefix

open SeaOfNodes.Diamond (Model Ty ValueSort dataPorts)
open RVSDG (Wires extend)
open RVSDG.NestedTheta (Term)
open Join (Choice Opcode)
open Join.Finite (Plan)
open Nested.Numbered (linkGamma splitSigs)
open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond (thenBase)
open Join (Block)
open Blocks (Bank)

universe u v w

variable {Data : Type u} {Op : SeaOfNodes.Diamond.Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {out : ValueSort Data} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size}

/-- The two split sites and their checked segments through the first
outer reconvergence. The source tail after this boundary belongs to the
enclosing profile. -/
structure Routes (src : Source Op regs out size) (entry : Fin size) extends Control src entry where
  meet : Fin size
  stop : Fin size
  innerTrue : Chain.Segment src meet onInnerTrue
  innerFalse : Chain.Segment src meet onInnerFalse
  suffix : Chain.Segment src stop meet
  outerFalse : Chain.Segment src stop onOuterFalse

/-- The legacy checked profile continues directly into its final join. -/
def ofProgram (p : Shared.Program src entry) : Routes src entry :=
  ⟨p.toControl, p.meet, p.join, p.innerTrue, p.innerFalse, p.suffix, p.outerFalse⟩

variable (p : Routes src entry)

/-- The predecessor and outgoing slot at the inner reconvergence. The
final jump of a nonempty prefix occupies slot zero. -/
def Routes.innerEdgeOccurrence (taken : Bool) : Fin size × Fin 2 :=
  match taken with
  | true => (p.innerTrue.predecessor p.inner, 0)
  | false => (p.innerFalse.predecessor p.inner, bif p.innerFalse.blocks.isEmpty then 1 else 0)

def Routes.prefixTarget : Occurrence → Fin size
  | .innerTrue | .innerFalse => p.meet
  | .outerFalse => p.stop

def Routes.prefixQuads (occurrence : Occurrence) : Block Op regs :=
  (src p.header).body ++ match occurrence with
  | .innerTrue => (src p.inner).body ++ p.innerTrue.quads
  | .innerFalse => (src p.inner).body ++ p.innerFalse.quads
  | .outerFalse => p.outerFalse.quads

/-- Each prefix supplies its independently compiled latest definitions. -/
def Routes.prefixTransfer (occurrence : Occurrence) :=
  CFG.compileBlock (p.prefixQuads occurrence) (initial regs)

/-- The shared segment takes a single full typed bank at the reconvergence. -/
def Routes.suffixTransfer :=
  CFG.compileBlock p.suffix.quads (initial regs)

def Routes.prefixBank (m : Model.{u, v, w} Op) (old : Bank (regs := regs) m)
    (occurrence : Occurrence) : Bank (regs := regs) m :=
  let compiled := p.prefixTransfer occurrence
  compiled.outgoing.read old (compiled.flow.eval m old PUnit.unit)

def Routes.suffixBank (m : Model.{u, v, w} Op) (incoming : Bank (regs := regs) m) : Bank (regs := regs) m :=
  let compiled := p.suffixTransfer
  compiled.outgoing.read incoming (compiled.flow.eval m incoming PUnit.unit)

def Routes.outerBank (m : Model.{u, v, w} Op) (old : Bank (regs := regs) m)
    (occurrence : Occurrence) : Bank (regs := regs) m :=
  let incoming := p.prefixBank m old occurrence
  match occurrence with
  | .innerTrue | .innerFalse => p.suffixBank m incoming
  | .outerFalse => incoming

def Routes.prefixVisits : Occurrence → Nat
  | .innerTrue => p.innerTrue.blocks.length + 2
  | .innerFalse => p.innerFalse.blocks.length + 2
  | .outerFalse => p.outerFalse.blocks.length + 1

def Routes.outerVisits (occurrence : Occurrence) : Nat :=
  p.prefixVisits occurrence + match occurrence with
    | .innerTrue | .innerFalse => p.suffix.blocks.length
    | .outerFalse => 0

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

/-- Link the header and both γs to a continuation over the actual outer
result wires. -/
def afterHeader {results : List (Ty Data)} {suffix : List (List (Ty Data))}
    (finish : Wires (dataPorts regs)
        (extend (extend [] (src p.header).body.producers) (splitSigs regs)) (dataPorts regs) →
      Term (Opcode Op) (dataPorts regs)
        (extend (extend [] (src p.header).body.producers) (splitSigs regs)) suffix results) :
    Term (Opcode Op) (dataPorts regs) []
      ((src p.header).body.producers ++ (splitSigs regs ++ suffix)) results :=
  thenBase ((src p.header).body.lowerFrom (initial regs) .jump) fun current =>
    afterOuter p current finish

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Prefix
