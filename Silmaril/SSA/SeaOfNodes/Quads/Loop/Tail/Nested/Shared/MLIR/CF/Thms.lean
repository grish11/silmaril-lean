module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.MLIR.CF.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.MLIR.CF.Correctness
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Thms

/-! # Exact typed CF observations after inner reconvergence -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.MLIR.CF

open SeaOfNodes.Diamond (ValueSort sortValue)
open SeaOfNodes.Loop.MLIR.CF (Op model evalOp)
open SeaOfNodes.MLIR (Word)
open SeaOfNodes.MLIR.Lowering (encodeValues valueBits valueWidth)
open Silmaril.MLIR.Arith (Width Env)
open Diamond.MLIR.CF (siteFrame lowerSource_run)
open Blocks (Bank)

variable {regs : List (ValueSort Width)} {out : ValueSort Width} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size} (p : Program src entry)
variable (input : Bank (regs := regs) model)

/-- The emitted path reaches the original reconvergence label on an
inner route, carrying the exact compiled prefix bank. -/
theorem from_header_eq_prefix (fuel : Nat) (old : Bank (regs := regs) model) :
    let occurrence := p.toControl.selected model old
    (lower p).runFrom evalOp (fuel + p.prefixVisits occurrence + 1) (encodeValues input) (siteFrame p.header old) =
      (lower p).runFrom evalOp (fuel + 1) (encodeValues input)
        (siteFrame (p.prefixTarget occurrence) (p.prefixBank model old occurrence)) :=
  Proofs.from_header_eq_prefix p input fuel old

/-- The actual CF run across the chosen prefix and any shared suffix
resumes at the original common merge with the compiled full bank. -/
theorem from_header_eq_merge (fuel : Nat) (old : Bank (regs := regs) model) :
    let occurrence := p.toControl.selected model old
    (lower p).runFrom evalOp (fuel + p.mergeVisits occurrence + 1) (encodeValues input) (siteFrame p.header old) =
      (lower p).runFrom evalOp (fuel + 1) (encodeValues input)
        (siteFrame p.join (p.mergeBank model old occurrence)) :=
  Proofs.from_header_eq_merge p input fuel old

/-- One extra visit executes the typed CF return. This also compares
exhaustion at every pair of corresponding budgets. -/
theorem lower_run (fuel : Nat) :
    (lower p).run evalOp (fuel + 1) (encodeValues input) =
      (src.runFrom model fuel entry input).map (fun value => Env.cons (valueBits value) .nil) :=
  lowerSource_run fuel input

theorem returns_iff (bits : Word (valueWidth out)) :
    (∃ cfFuel, (lower p).run evalOp cfFuel (encodeValues input) = some (.cons bits .nil)) ↔
      ∃ (fuel : Nat) (value : sortValue Word out), src.runFrom model fuel entry input = some value ∧ valueBits value = bits :=
  Proofs.returns_iff p input bits

theorem noFiniteReturn_iff :
    (lower p).Diverges evalOp (encodeValues input) ↔ ∀ fuel, src.runFrom model fuel entry input = none :=
  Proofs.noFiniteReturn_iff p input

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.MLIR.CF
