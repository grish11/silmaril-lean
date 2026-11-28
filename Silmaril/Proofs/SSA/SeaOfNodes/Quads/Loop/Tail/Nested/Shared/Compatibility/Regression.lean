module

import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Numbered.Petri.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Thms

/-! Pre-#4390 dependent types for clients of the inner-only profile. -/

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared

open SeaOfNodes.Diamond (Model Ty ValueSort dataPorts sortValue)
open RVSDG (Wires extend)
open RVSDG.NestedTheta (Graph Term)
open RVSDG.NestedTheta.Petri (Finishes)
open Join (Block Opcode model)
open Join.Finite (Plan)
open Nested.Numbered (splitSigs)
open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond (bodyPorts)
open Blocks (Bank)

universe u v w

variable {Data : Type u} {Op : SeaOfNodes.Diamond.Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {out : ValueSort Data} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size}
variable (p : Program src entry) (m : Model.{u, v, w} Op)
variable (old : Bank (regs := regs) m) (fuel : Nat)

example : Option (Program src entry) := check src entry

example (control : Control src entry) (meet : Fin size)
    (yes : Chain.Segment src meet control.onInnerTrue) (no : Chain.Segment src meet control.onInnerFalse)
    (suffix : Chain.Segment src control.join meet)
    (outerFalse : Chain.Segment src control.join control.onOuterFalse) : Option (Program src entry) :=
  Program.admit control meet yes no suffix outerFalse

example (control : Control src entry) (meet : Fin size)
    (yes : Chain.Segment src meet control.onInnerTrue) (no : Chain.Segment src meet control.onInnerFalse)
    (suffix : Chain.Segment src control.join meet) (outerFalse : Chain.Segment src control.join control.onOuterFalse)
    (nonempty : suffix.blocks ≠ [])
    (distinct : ([entry, control.header, control.inner] ++ yes.blocks ++ no.blocks ++ suffix.blocks ++
      outerFalse.blocks ++ [control.join, control.latch]).Nodup)
    (covers : ([entry, control.header, control.inner] ++ yes.blocks ++ no.blocks ++ suffix.blocks ++
      outerFalse.blocks ++ [control.join, control.latch]).length = size) : Program src entry :=
  Program.mk control meet yes no suffix outerFalse nonempty distinct covers

example : Chain.Segment src p.meet p.onInnerTrue := p.innerTrue
example : Chain.Segment src p.meet p.onInnerFalse := p.innerFalse
example : Chain.Segment src p.join p.meet := p.suffix
example : Chain.Segment src p.join p.onOuterFalse := p.outerFalse

example : ([entry, p.header, p.inner] ++ p.innerTrue.blocks ++ p.innerFalse.blocks ++ p.suffix.blocks ++
    p.outerFalse.blocks ++ [p.join, p.latch]).Nodup := p.distinct

example : ([entry, p.header, p.inner] ++ p.innerTrue.blocks ++ p.innerFalse.blocks ++ p.suffix.blocks ++
    p.outerFalse.blocks ++ [p.join, p.latch]).length = size := p.covers

example : p.prefixTarget .outerFalse = p.join := rfl
example : Occurrence → Block Op regs := p.prefixQuads

example (occurrence : Occurrence) :
    Loop.Transfer Op regs (dataPorts regs) [] (p.prefixQuads occurrence).producers := p.prefixTransfer occurrence

example : Loop.Transfer Op regs (dataPorts regs) [] p.suffix.quads.producers := p.suffixTransfer

example : p.innerEdgeOccurrence true ≠ p.innerEdgeOccurrence false := p.inner_edges_distinct

example (occurrence : Occurrence) :
    p.prefixBank m old occurrence = (p.prefixQuads occurrence).eval m old := p.prefix_bank m old occurrence

example : p.suffixBank m old = p.suffix.quads.eval m old := p.suffix_bank m old

example :
    let occurrence := p.toControl.selected m old
    src.runFrom m (fuel + p.prefixVisits occurrence) p.header old =
      src.runFrom m fuel (p.prefixTarget occurrence) (p.prefixBank m old occurrence) :=
  p.run_prefix m old fuel

example : src.runFrom m (fuel + p.suffix.blocks.length) p.meet old =
    src.runFrom m fuel p.join (p.suffixBank m old) :=
  p.run_suffix m old fuel

example :
    let occurrence := p.toControl.selected m old
    src.runFrom m (fuel + p.mergeVisits occurrence) p.header old =
      src.runFrom m fuel p.join (p.mergeBank m old occurrence) :=
  p.run_to_merge m old fuel

example : Plan Op regs := Numbered.innerPlan p

example : Term (Opcode Op) (dataPorts regs) []
    ((src p.inner).body.producers ++ ((Numbered.innerPlan p).producers ++ p.suffix.quads.producers))
    (dataPorts regs) := Numbered.innerRegion p

example (i : Fin 2) : Term (Opcode Op) (dataPorts regs) [] (Numbered.outerSigs p i) (dataPorts regs) :=
  Numbered.outerArm p i

example {args results : List (Ty Data)} {past suffix : List (List (Ty Data))}
    (current : Wires args past (dataPorts regs))
    (finish : Wires args (extend past (splitSigs regs)) (dataPorts regs) →
      Term (Opcode Op) args (extend past (splitSigs regs)) suffix results) :
    Term (Opcode Op) args past (splitSigs regs ++ suffix) results :=
  Numbered.afterOuter p current finish

example : Term (Opcode Op) (dataPorts regs) []
    ((src p.header).body.producers ++ splitSigs regs) (dataPorts regs) := Numbered.mergeRegion p

example : Term (Opcode Op) (dataPorts regs) []
    ((src p.header).body.producers ++ (splitSigs regs ++ ((Numbered.tail p).producers ++ [bodyPorts regs])))
    (bodyPorts regs) := Numbered.thetaBody p

example : Term (Opcode Op) (dataPorts regs) [] ((src entry).body.producers ++ [dataPorts regs]) [.value out] :=
  Numbered.lowerTerm p

example : Graph (Opcode Op) (dataPorts regs) [] ((src entry).body.producers ++ [dataPorts regs]) [.value out] :=
  Numbered.lower p

example : (Numbered.mergeRegion p).toGraph.run (model m) fuel old =
    some (p.mergeBank m old (p.toControl.selected m old)) :=
  Numbered.merge_run p m fuel old

example : (Numbered.thetaBody p).toGraph.run (model m) fuel old =
    let next := Numbered.nextBank p m old
    some (RVSDG.Theta.bodyResult (model m) (next.get p.again).down next) :=
  Numbered.activation_run p m fuel old

example : (Numbered.lower p).run (model m) fuel old =
    (src.runFrom m (Numbered.sourceVisits p m fuel old) entry old).map (fun x => .cons x .nil) :=
  Numbered.lower_run p m fuel old

example (value : sortValue m.value out) :
    (Numbered.lower p).Returns (model m) old (.cons value .nil) ↔
      ∃ fuel, src.runFrom m fuel entry old = some value := Numbered.returns_iff p m old value

example : (∀ fuel, (Numbered.lower p).run (model m) fuel old = none) ↔
    ∀ fuel, src.runFrom m fuel entry old = none := Numbered.noFiniteReturn_iff p m old

example (value : sortValue m.value out) :
    Finishes (model m) (Numbered.lower p) old (.cons value .nil) ↔
      ∃ fuel, src.runFrom m fuel entry old = some value := Numbered.petri_finishes_iff p m old value

example : Option (Outer.Program src entry) := Outer.check src entry

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared
