module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Defs
public import Silmaril.SSA.MLIR.CF.SwitchAssert.Denotation.Defs
public import Silmaril.SSA.RVSDG.NestedTheta.Categorical.Defs
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.Prune.Thms
import Silmaril.SSA.MLIR.CF.SwitchAssert.Denotation.Thms
import Silmaril.SSA.MLIR.CF.SwitchAssert.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Categorical.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Comparison.Proofs

open SeaOfNodes.Diamond (Val ValueSort)
open SeaOfNodes.Loop.MLIR.CF (Op model evalOp)
open SeaOfNodes.MLIR (Word)
open SeaOfNodes.MLIR.Lowering (encodeValues valueWidth)
open Silmaril.MLIR.Arith (Env Width)
open Silmaril.MLIR.CF.SwitchAssert (Cfg Outcome)
open RVSDG (Tuple)
open RVSDG.NestedTheta (Graph)
open Blocks (Bank)
open Blocks.Prune (Mask)
open Diamond.Prune (Checked)

variable {regs : List (ValueSort Width)} {out : ValueSort Width} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size}
variable {p : Program src entry} {mask : Mask regs}
variable (checked : Checked p mask) (input : Bank (regs := regs) model)

theorem run_at_source_visits (activations : Nat) :
    (lower checked).run evalOp (p.sourceVisits model activations input + 1) (encodeValues input) =
      (checked.lower.run (Join.model model) activations input).map (encodeValues (ins := [out])) := by
  rw [Pruned.lower_run, checked.lower_run]
  cases src.runFrom model (p.sourceVisits model activations input) entry input <;> rfl

theorem returns_iff (output : Env [valueWidth out]) :
    (∃ fuel, (lower checked).run evalOp fuel (encodeValues input) = some output) ↔
      ∃ activations,
        (checked.lower.run (Join.model model) activations input).map (encodeValues (ins := [out])) = some output := by
  constructor
  · rintro ⟨_ | fuel, returned⟩
    · cases returned
    · rw [Pruned.lower_run, Option.map_eq_some_iff] at returned
      obtain ⟨value, sourceRun, rfl⟩ := returned
      obtain ⟨activations, graphRun⟩ := (checked.returns_iff model input value).mpr ⟨fuel, sourceRun⟩
      exact ⟨activations, by rw [graphRun]; rfl⟩
  · rintro ⟨activations, graphRun⟩
    exact ⟨_, (run_at_source_visits checked input activations).trans graphRun⟩

theorem denotePart_eq :
    (Cfg.embed (lower checked)).denotePart evalOp (encodeValues input) =
      (checked.lower.denotePart (Join.model model) input).map
        (fun values => Outcome.returned (encodeValues (ins := [out]) values)) := by
  have graphMem (values : Tuple (Val Word) [.value out]) :
      values ∈ checked.lower.denotePart (Join.model model) input ↔
        ∃ activations, checked.lower.run (Join.model model) activations input = some values :=
    (checked.lower.mem_denote (Join.model model) input values).trans
      (checked.lower.returns_iff (Join.model model) input values).symm
  apply Part.ext
  intro outcome
  rw [Cfg.mem_denotePart_iff]
  simp only [Cfg.embed_run, Option.map_eq_some_iff]
  constructor
  · rintro ⟨fuel, output, cfRun, rfl⟩
    obtain ⟨activations, graphRun⟩ := (returns_iff checked input output).mp ⟨fuel, cfRun⟩
    obtain ⟨values, observed, rfl⟩ := Option.map_eq_some_iff.mp graphRun
    exact Part.mem_map _ ((graphMem values).mpr ⟨activations, observed⟩)
  · intro observed
    obtain ⟨values, graphDenote, rfl⟩ := (Part.mem_map_iff _).mp observed
    obtain ⟨activations, graphRun⟩ := (graphMem values).mp graphDenote
    exact ⟨_, _, (run_at_source_visits checked input activations).trans
      (congrArg (Option.map (encodeValues (ins := [out]))) graphRun), rfl⟩

theorem source_diverges_iff :
    (∀ fuel, src.runFrom model fuel entry input = none) ↔
      (lower checked).Diverges evalOp (encodeValues input) := by
  change _ ↔ ∀ fuel, (lower checked).run evalOp fuel (encodeValues input) = none
  constructor
  · intro exhausted fuel
    cases fuel with
    | zero => rfl
    | succ fuel => rw [Pruned.lower_run, exhausted]; rfl
  · intro exhausted fuel
    have run := exhausted (fuel + 1)
    rw [Pruned.lower_run, Option.map_eq_none_iff] at run
    exact run

theorem diverges_iff :
    (lower checked).Diverges evalOp (encodeValues input) ↔
      ∀ activations, checked.lower.run (Join.model model) activations input = none := by
  calc
    _ ↔ ¬ (checked.lower.denotePart (Join.model model) input).Dom := by
      rw [← Cfg.embed_diverges_iff, ← Cfg.denotePart_eq_none_iff, denotePart_eq, Part.eq_none_iff']
      rfl
    _ ↔ _ := by
      rw [← Part.eq_none_iff', Graph.denotePart_eq_none]
      simp only [← Graph.returns_iff, Graph.Returns, not_exists, Option.eq_none_iff_forall_ne_some]
      exact forall_comm

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Comparison.Proofs
