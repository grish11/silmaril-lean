module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.MLIR.CF.Defs
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.MLIR.CF.Proofs

open SeaOfNodes.Diamond (ValueSort sortValue)
open SeaOfNodes.Loop.MLIR.CF (Op model evalOp)
open SeaOfNodes.MLIR (Word)
open SeaOfNodes.MLIR.Lowering (encodeValues valueBits valueWidth)
open Silmaril.MLIR.Arith (Width Env)
open Diamond.MLIR.CF (siteFrame source_site_eval lowerSource_run runBlock_eq_of_frames)
open Blocks (Bank)

variable {regs : List (ValueSort Width)} {out : ValueSort Width} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size} (p : Program src entry)
variable (input : Bank (regs := regs) model)

theorem outer_arrival (old : Bank (regs := regs) model) :
    let occurrence := p.toControl.selected model old
    outerArrival p input old = .inl (siteFrame p.stop (p.outerBank model old occurrence)) := by
  have edge := p.selected_outer_edge model old
  dsimp only at edge ⊢
  unfold outerArrival lower
  rw [source_site_eval, edge.1, edge.2]
  rfl

private theorem lower_from_site (fuel : Nat) (id : Fin size) (old : Bank (regs := regs) model) :
    (lower p).runFrom evalOp (fuel + 1) (encodeValues input) (siteFrame id old) =
      (src.runFrom model fuel id old).map (fun value => Env.cons (valueBits value) .nil) :=
  runBlock_eq_of_frames (src := src) (lower p) input siteFrame .exit
    (fun id old => source_site_eval input old id) rfl fuel id old _ _ (source_site_eval input old id)

theorem from_header_eq_tail (fuel : Nat) (old : Bank (regs := regs) model) :
    let occurrence := p.toControl.selected model old
    (lower p).runFrom evalOp (fuel + p.outerVisits occurrence + 1) (encodeValues input) (siteFrame p.header old) =
      (lower p).runFrom evalOp (fuel + 1) (encodeValues input) (siteFrame p.stop (p.outerBank model old occurrence)) := by
  dsimp only
  rw [lower_from_site, lower_from_site, p.run_to_outer]

theorem source_returns_iff (output : Env [valueWidth out]) :
    (∃ cfFuel, (lower p).run evalOp cfFuel (encodeValues input) = some output) ↔
      ∃ (sourceFuel : Nat) (value : sortValue Word out),
        src.runFrom model sourceFuel entry input = some value ∧ encodeValues (ins := [out]) (.cons value .nil) = output := by
  constructor
  · rintro ⟨_ | fuel, returned⟩
    · cases returned
    · rw [lower, lowerSource_run] at returned
      exact ⟨fuel, Option.map_eq_some_iff.mp returned⟩
  · rintro ⟨fuel, value, returned, encoded⟩
    exact ⟨fuel + 1, by rw [lower, lowerSource_run, returned]; exact congrArg some encoded⟩

theorem source_noFiniteReturn_iff :
    (lower p).Diverges evalOp (encodeValues input) ↔ ∀ fuel, src.runFrom model fuel entry input = none := by
  constructor
  · intro absent fuel
    have exhausted := absent (fuel + 1)
    rw [lower, lowerSource_run] at exhausted
    exact Option.map_eq_none_iff.mp exhausted
  · intro absent fuel
    cases fuel with
    | zero => rfl
    | succ fuel => rw [lower, lowerSource_run, absent]; rfl

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.MLIR.CF.Proofs
