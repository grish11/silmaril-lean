module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MLIR.CF.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Numbered.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MLIR.CF.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Numbered.Comparison.Proofs

open SeaOfNodes.Diamond (ValueSort)
open SeaOfNodes.Loop.MLIR.CF (Op evalOp model)
open SeaOfNodes.MLIR.Lowering (encodeValues valueWidth)
open Silmaril.MLIR.Arith (Env Width)
open Diamond.Prune (HeaderProjection)
open Blocks (Bank)
open Blocks.Prune (Mask)

variable {regs : List (ValueSort Width)} {out : ValueSort Width} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size} {mask : Mask regs}
variable (p : Program src entry) (projected : HeaderProjection (src p.header).body mask)
variable (result : KeptResult p (mask := mask)) (input : Bank (regs := regs) model)

theorem cf_at_activations (activations : Nat) :
    (Nested.MLIR.CF.lower p projected).run evalOp (sourceVisits p model activations input + 1) (encodeValues input) =
      ((lower p projected result).run (Join.model model) activations input).map
        (encodeValues (ins := [out])) := by
  rw [Nested.MLIR.CF.lower_run, Numbered.lower_run]
  cases src.runFrom model (sourceVisits p model activations input) entry input <;> rfl

theorem cf_returns_iff (output : Env [valueWidth out]) :
    (∃ visits, (Nested.MLIR.CF.lower p projected).run evalOp visits (encodeValues input) = some output) ↔
      ∃ activations, ((lower p projected result).run (Join.model model) activations input).map
        (encodeValues (ins := [out])) = some output := by
  constructor
  · rintro ⟨_ | visits, returned⟩
    · cases returned
    · rw [Nested.MLIR.CF.lower_run, Option.map_eq_some_iff] at returned
      obtain ⟨value, observed, rfl⟩ := returned
      obtain ⟨activations, native⟩ := (Numbered.returns_iff p model projected result input value).mpr
        ⟨visits, observed⟩
      exact ⟨activations, by rw [native]; rfl⟩
  · rintro ⟨activations, returned⟩
    exact ⟨_, (cf_at_activations p projected result input activations).trans returned⟩

theorem cf_diverges_iff :
    (Nested.MLIR.CF.lower p projected).Diverges evalOp (encodeValues input) ↔
      ∀ activations, (lower p projected result).run (Join.model model) activations input = none := by
  constructor
  · intro exhausted activations
    exact Option.map_eq_none_iff.mp
      ((cf_at_activations p projected result input activations).symm.trans (exhausted _))
  · intro exhausted visits
    cases returned : (Nested.MLIR.CF.lower p projected).run evalOp visits (encodeValues input) with
    | none => rfl
    | some output =>
      obtain ⟨activations, native⟩ := (cf_returns_iff p projected result input output).mp ⟨visits, returned⟩
      rw [exhausted activations] at native
      cases native

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Numbered.Comparison.Proofs
