module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.MLIR.CF.Thms
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Petri.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.MLIR.CF.Comparison.Proofs

open SeaOfNodes.Diamond (ValueSort)
open SeaOfNodes.Loop.MLIR.CF (Op model evalOp)
open SeaOfNodes.MLIR.Lowering (encodeValues valueWidth)
open Silmaril.MLIR.Arith (Width Env)
open Diamond.MLIR.CF (siteFrame exitFrame source_site_eval)
open RVSDG.NestedTheta.Petri (Finishes finishes_iff)
open Blocks (Bank)

variable {regs : List (ValueSort Width)} {out : ValueSort Width} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size} (p : Program src entry)
variable (input : Bank (regs := regs) model)

theorem latch_successor (old : Bank (regs := regs) model) :
    let next := Outer.Numbered.nextBank p model old
    latchSuccessor p input old =
      .inl (if (next.get p.again).down then siteFrame p.header next else exitFrame (next.get p.result)) := by
  dsimp only
  unfold latchSuccessor CF.lower
  rw [source_site_eval, p.latchEdge]
  have postLatch : Outer.Numbered.nextBank p model old =
      (src p.latch).body.eval model ((src p.join).body.eval model
        (p.mergeBank model old (p.toControl.selected model old))) := List.foldl_append
  rw [← postLatch]
  by_cases again : (((Outer.Numbered.nextBank p model old).get p.again).down) = true
  · rw [Tail.Terminator.select, ite_eq_left again, ite_eq_left again]
    rfl
  · rw [Tail.Terminator.select, ite_eq_right again, ite_eq_right again]
    rfl

theorem cf_finishes_iff (output : Env [valueWidth out]) :
    (∃ cfFuel, (CF.lower p).run evalOp cfFuel (encodeValues input) = some output) ↔
      ∃ packet, Finishes (Join.model model) (Outer.Numbered.lower p) input packet ∧
        encodeValues (ins := [out]) packet = output := by
  refine (source_returns_iff p input output).trans ?_
  constructor
  · rintro ⟨fuel, value, returned, encoded⟩
    exact ⟨.cons value .nil, (Outer.Numbered.petri_finishes_iff p model input value).mpr ⟨fuel, returned⟩, encoded⟩
  · rintro ⟨packet, complete, encoded⟩
    cases packet with
    | cons value rest =>
      cases rest
      obtain ⟨fuel, returned⟩ := (Outer.Numbered.petri_finishes_iff p model input value).mp complete
      exact ⟨fuel, value, returned, encoded⟩

theorem cf_returns_iff (output : Env [valueWidth out]) :
    (∃ cfFuel, (CF.lower p).run evalOp cfFuel (encodeValues input) = some output) ↔
      ∃ activations, ((Outer.Numbered.lower p).run (Join.model model) activations input).map
        (encodeValues (ins := [out])) = some output := by
  refine (source_returns_iff p input output).trans ?_
  constructor
  · rintro ⟨fuel, value, returned, encoded⟩
    obtain ⟨activations, ran⟩ := (Outer.Numbered.returns_iff p model input value).mpr ⟨fuel, returned⟩
    exact ⟨activations, Option.map_eq_some_iff.mpr ⟨.cons value .nil, ran, encoded⟩⟩
  · rintro ⟨activations, returned⟩
    obtain ⟨packet, ran, encoded⟩ := Option.map_eq_some_iff.mp returned
    cases packet with
    | cons value rest =>
      cases rest
      obtain ⟨fuel, returned⟩ := (Outer.Numbered.returns_iff p model input value).mp ⟨activations, ran⟩
      exact ⟨fuel, value, returned, encoded⟩

theorem cf_noCompletion_iff :
    (CF.lower p).Diverges evalOp (encodeValues input) ↔
      ∀ packet, ¬ Finishes (Join.model model) (Outer.Numbered.lower p) input packet := by
  rw [source_noFiniteReturn_iff, ← Outer.Numbered.noFiniteReturn_iff p model input]
  constructor
  · intro absent packet finished
    obtain ⟨activations, returned⟩ := (finishes_iff _ _ _ _).mp finished
    rw [absent] at returned
    cases returned
  · intro absent fuel
    cases returned : (Outer.Numbered.lower p).run (Join.model model) fuel input with
    | none => rfl
    | some packet =>
      exact (absent packet ((finishes_iff _ _ _ _).mpr ⟨fuel, returned⟩)).elim

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.MLIR.CF.Comparison.Proofs
