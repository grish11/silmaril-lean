module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.MLIR.CF.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.MLIR.CF.Correctness
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Thms

/-! # Exact outer arrivals in the existing typed CF emitter -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.MLIR.CF

open SeaOfNodes.Diamond (ValueSort sortValue)
open SeaOfNodes.Loop.MLIR.CF (Op model evalOp)
open SeaOfNodes.MLIR (Word)
open SeaOfNodes.MLIR.Lowering (encodeValues valueBits valueWidth)
open Silmaril.MLIR.Arith (Width Env)
open Diamond.MLIR.CF (Label siteFrame lowerSource_run)
open Blocks (Bank)

variable {regs : List (ValueSort Width)} {out : ValueSort Width} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size} (p : Program src entry)
variable (input : Bank (regs := regs) model)

/-- The two original incoming CF blocks have distinct labels. The shared
destination frame itself contains only the target and its typed operands. -/
theorem outer_arrival_sites_distinct :
    (Label.site (out := out) (regs := regs) (p.outerEdgeOccurrence true).1) ≠
      Label.site (p.outerEdgeOccurrence false).1 :=
  fun same => p.outer_predecessors_distinct (Label.site.inj same)

/-- The actual selected predecessor targets the same original tail label
on both outer routes, passing the complete encoded reaching bank. -/
theorem outer_arrival (old : Bank (regs := regs) model) :
    let occurrence := p.toControl.selected model old
    outerArrival p input old = .inl (siteFrame p.stop (p.outerBank model old occurrence)) :=
  Proofs.outer_arrival p input old

theorem from_header_eq_tail (fuel : Nat) (old : Bank (regs := regs) model) :
    let occurrence := p.toControl.selected model old
    (lower p).runFrom evalOp (fuel + p.outerVisits occurrence + 1) (encodeValues input) (siteFrame p.header old) =
      (lower p).runFrom evalOp (fuel + 1) (encodeValues input) (siteFrame p.stop (p.outerBank model old occurrence)) :=
  Proofs.from_header_eq_tail p input fuel old

/-- Typed CF adds only its final return block to the source visit count. -/
theorem lower_run (fuel : Nat) :
    (lower p).run evalOp (fuel + 1) (encodeValues input) =
      (src.runFrom model fuel entry input).map (fun value => Env.cons (valueBits value) .nil) :=
  lowerSource_run fuel input

theorem source_returns_iff (output : Env [valueWidth out]) :
    (∃ cfFuel, (lower p).run evalOp cfFuel (encodeValues input) = some output) ↔
      ∃ (sourceFuel : Nat) (value : sortValue Word out),
        src.runFrom model sourceFuel entry input = some value ∧ encodeValues (ins := [out]) (.cons value .nil) = output :=
  Proofs.source_returns_iff p input output

theorem source_noFiniteReturn_iff :
    (lower p).Diverges evalOp (encodeValues input) ↔ ∀ fuel, src.runFrom model fuel entry input = none :=
  Proofs.source_noFiniteReturn_iff p input

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.MLIR.CF
