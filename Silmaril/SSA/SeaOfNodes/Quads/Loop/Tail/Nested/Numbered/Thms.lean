module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Numbered.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Numbered.Correctness

/-! # Occurrence-resolved γ banks and finite returns of the numbered θ -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Numbered

open SeaOfNodes.Diamond (Model Ty Val ValueSort dataPorts sortValue)
open RVSDG (Locals Tuple Wires extend)
open RVSDG.NestedTheta (Term)
open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond (bodyPorts)
open Diamond.Prune (HeaderProjection)
open Join (Opcode model)
open Blocks (Bank)
open Blocks.Prune (Mask)

universe u v w

variable {Data : Type u} {Op : SeaOfNodes.Diamond.Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {out : ValueSort Data} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size} {mask : Mask regs}
variable (p : Program src entry) (m : Model.{u, v, w} Op)
variable (projected : HeaderProjection (src p.header).body mask)

/-- The emitted outer γ arm delivers the bank of its selected region. -/
theorem outerArm_run (fuel : Nat) (bank : Bank (regs := regs) m) :
    (outerArm p ((outerChoice p).eval bank)).run (model m) fuel bank =
      some (branchBank p m bank) :=
  Proofs.outerArm_run p m fuel bank

/-- The continuation observes only the actual selected arm result. -/
theorem linkGamma_eval {args outputs results : List (Ty Data)} {past suffix : List (List (Ty Data))}
    (choice : Join.Choice regs 2) (sigs : Fin 2 → List (List (Ty Data)))
    (arms : (i : Fin 2) → Term (Opcode Op) (dataPorts regs) [] (sigs i) outputs)
    (current : Wires args past (dataPorts regs))
    (finish : Wires args (extend past [routePorts regs, outputs]) outputs →
      Term (Opcode Op) args (extend past [routePorts regs, outputs]) suffix results)
    (fuel : Nat) (input : Tuple (Val m.value) args) (locals : Locals (Val m.value) past)
    (selected : Bank (regs := regs) m → Tuple (Val m.value) outputs)
    (arm_agrees : ∀ bank, (arms (choice.eval bank)).run (model m) fuel bank = some (selected bank))
    (observe : Tuple (Val m.value) outputs → Option (Tuple (Val m.value) results))
    (agrees : ∀ wires locals', (finish wires).eval (model m) fuel input locals' =
      observe (wires.read input locals')) :
    (linkGamma choice sigs arms current finish).eval (model m) fuel input locals =
      observe (selected (current.read input locals)) :=
  Proofs.linkGamma_eval m choice sigs arms current finish fuel input locals selected arm_agrees observe agrees

/-- The outer selector and γ preserve the supplied arm result interface. -/
theorem afterOuterWith_eval {args outputs results : List (Ty Data)} {past suffix : List (List (Ty Data))}
    (arms : (i : Fin 2) → Term (Opcode Op) (dataPorts regs) [] (outerSigs p i) outputs)
    (current : Wires args past (dataPorts regs))
    (finish : Wires args (extend past [routePorts regs, outputs]) outputs →
      Term (Opcode Op) args (extend past [routePorts regs, outputs]) suffix results)
    (fuel : Nat) (input : Tuple (Val m.value) args) (locals : Locals (Val m.value) past)
    (selected : Bank (regs := regs) m → Tuple (Val m.value) outputs)
    (arm_agrees : ∀ bank, (arms ((outerChoice p).eval bank)).run (model m) fuel bank = some (selected bank))
    (observe : Tuple (Val m.value) outputs → Option (Tuple (Val m.value) results))
    (agrees : ∀ wires locals', (finish wires).eval (model m) fuel input locals' =
      observe (wires.read input locals')) :
    (afterOuterWith p arms current finish).eval (model m) fuel input locals =
      observe (selected (current.read input locals)) :=
  Proofs.afterOuterWith_eval p m arms current finish fuel input locals selected arm_agrees observe agrees

/-- The selected source path reads its independently compiled occurrence. -/
theorem branchBank_agrees (old : Bank (regs := regs) m) :
    branchBank p m ((src p.header).body.eval m old) =
      p.mergeBank m old (p.selected m old) :=
  Proofs.branchBank_agrees p m old

/-- A body that implements one checked activation gives the same source observation at the selected visit bound. -/
theorem lowerWith_run {bodySigs : List (List (Ty Data))}
    (body : Term (Opcode Op) (dataPorts mask.kept) [] bodySigs (bodyPorts mask.kept))
    (activation : ∀ fuel old, body.run (model m) fuel (mask.project old) =
      let next := nextBank p m old
      some (RVSDG.Theta.bodyResult (model m) (next.get p.again).down (mask.project next)))
    (result : KeptResult p (mask := mask)) (fuel : Nat) (input : Bank (regs := regs) m) :
    (lowerWith p result body).run (model m) fuel input =
      (src.runFrom m (sourceVisits p m fuel input) entry input).map (fun value => .cons value .nil) :=
  Proofs.lowerWith_run p m body activation result fuel input

/-- The two emitted γ selections supply the entire original source column
at whichever of the three incoming occurrences is selected. -/
theorem merge_run (fuel : Nat) (old : Bank (regs := regs) m) :
    (mergeRegion p projected).toGraph.run (model m) fuel (mask.project old) =
      some (p.mergeBank m old (p.selected m old)) :=
  Proofs.merge_run p m projected fuel old

/-- A θ activation returns the post-latch stop tag and simultaneous projected feedback. -/
theorem activation_run (fuel : Nat) (old : Bank (regs := regs) m) :
    (thetaBody p projected).run (model m) fuel (mask.project old) =
      let next := nextBank p m old
      some (RVSDG.Theta.bodyResult (model m) (next.get p.again).down (mask.project next)) :=
  Proofs.activation_run p m projected fuel old

/-- One source visit per original block on the selected paths accounts for
the native bound, including runs that exhaust at that bound. -/
theorem lower_run (result : KeptResult p (mask := mask)) (fuel : Nat) (input : Bank (regs := regs) m) :
    (lower p projected result).run (model m) fuel input =
      (src.runFrom m (sourceVisits p m fuel input) entry input).map (fun value => .cons value .nil) :=
  Proofs.lower_run p m projected result fuel input

/-- A finite return of the original source is witnessed at some activation
bound in the emitted graph, and vice versa. -/
theorem returns_iff (result : KeptResult p (mask := mask)) (input : Bank (regs := regs) m)
    (value : sortValue m.value out) :
    (lower p projected result).Returns (model m) input (.cons value .nil) ↔
      ∃ fuel, src.runFrom m fuel entry input = some value :=
  Proofs.returns_iff p m projected result input value

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Numbered
