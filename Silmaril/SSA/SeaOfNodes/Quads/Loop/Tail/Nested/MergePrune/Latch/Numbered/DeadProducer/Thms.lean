module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.Numbered.DeadProducer.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.Numbered.DeadProducer.Correctness
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.Numbered.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.Split.DeadProducer.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Numbered.Thms

/-! # Exact latch observations and finite returns of the shortened numbered θ -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.Numbered.DeadProducer

open SeaOfNodes.Diamond (Model ValueSort dataPorts sortValue)
open SeaOfNodes.Pure.Deletion.Iteration (Table)
open Diamond.Prune (HeaderProjection)
open Join (model)
open Nested.Numbered (KeptResult nextBank sourceVisits)
open Blocks (Bank)
open Blocks.Prune (Mask)

universe u v w

variable {Data : Type u} {Op : SeaOfNodes.Diamond.Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {out : ValueSort Data} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size} {carry merge atLatch : Mask regs}
variable (p : Program src entry) (m : Model.{u, v, w} Op)
variable (projected : HeaderProjection (src p.header).body carry)
variable (checked : Split.Checked p carry merge atLatch)
section Table

variable (table : Table Op (dataPorts atLatch.kept) (packetPorts out carry))
variable (same : ∀ old, table.eval m old = checked.latchTransfer.eval m old)
include same

/-- The emitted prefix reads the guard, exit and feedback after the
original γs resolve the selected predecessor. -/
theorem packetWith_run (fuel : Nat) (old : Bank (regs := regs) m) :
    (packetWith p projected checked table).toGraph.run (model m) fuel (carry.project old) =
      some (observe p carry (nextBank p m old)) :=
  Proofs.packetWith_run m checked table projected same fuel old

/-- The emitted θ body latches the original projected feedback together. -/
theorem thetaWith_run (fuel : Nat) (old : Bank (regs := regs) m) :
    (thetaWith p projected checked table).run (model m) fuel (carry.project old) =
      some (MergePrune.Numbered.latchPacket p carry m (nextBank p m old)) :=
  Proofs.thetaWith_run m checked table projected same fuel old

variable (result : KeptResult p (mask := carry)) (input : Bank (regs := regs) m)

theorem lowerWith_run (fuel : Nat) :
    (lowerWith p projected checked table result).run (model m) fuel input =
      (src.runFrom m (sourceVisits p m fuel input) entry input).map (fun value => .cons value .nil) :=
  Nested.Numbered.lowerWith_run p m _ (thetaWith_run p m projected checked table same) result fuel input

theorem lowerWith_run_agrees (fuel : Nat) :
    (lowerWith p projected checked table result).run (model m) fuel input =
      (Numbered.lower p projected checked.whole result).run (model m) fuel input :=
  (lowerWith_run p m projected checked table same result input fuel).trans
    (Numbered.lower_run p m projected checked.whole result fuel input).symm

theorem lowerWith_returns_iff (value : sortValue m.value out) :
    (lowerWith p projected checked table result).Returns (model m) input (.cons value .nil) ↔
      ∃ fuel, src.runFrom m fuel entry input = some value :=
  (exists_congr fun fuel => by rw [lowerWith_run_agrees p m projected checked table same result input fuel]).trans
    (Numbered.returns_iff p m projected checked.whole result input value)

theorem lowerWith_noFiniteReturn_iff :
    (∀ fuel, (lowerWith p projected checked table result).run (model m) fuel input = none) ↔
      ∀ fuel, src.runFrom m fuel entry input = none := by
  refine ⟨fun h fuel => Option.eq_none_iff_forall_ne_some.mpr (fun value found => ?_),
    fun h fuel => by rw [lowerWith_run p m projected checked table same, h]; rfl⟩
  obtain ⟨bound, returned⟩ := (lowerWith_returns_iff p m projected checked table same result input value).2 ⟨fuel, found⟩
  exact Option.eq_none_iff_forall_ne_some.mp (h bound) _ returned

end Table

variable (cut : Split.DeadProducer.Checked checked.latchTransfer)

theorem packet_run (fuel : Nat) (old : Bank (regs := regs) m) :
    (packetRegion p projected checked cut).toGraph.run (model m) fuel (carry.project old) =
      some (observe p carry (nextBank p m old)) :=
  packetWith_run p m projected checked cut.table (cut.eval_agrees m) fuel old

theorem activation_run (fuel : Nat) (old : Bank (regs := regs) m) :
    (thetaBody p projected checked cut).run (model m) fuel (carry.project old) =
      some (MergePrune.Numbered.latchPacket p carry m (nextBank p m old)) :=
  thetaWith_run p m projected checked cut.table (cut.eval_agrees m) fuel old

variable (result : KeptResult p (mask := carry)) (input : Bank (regs := regs) m)

theorem lower_run (fuel : Nat) :
    (lower p projected checked cut result).run (model m) fuel input =
      (src.runFrom m (sourceVisits p m fuel input) entry input).map (fun value => .cons value .nil) :=
  lowerWith_run p m projected checked cut.table (cut.eval_agrees m) result input fuel

theorem run_agrees (fuel : Nat) :
    (lower p projected checked cut result).run (model m) fuel input =
      (Numbered.lower p projected checked.whole result).run (model m) fuel input :=
  lowerWith_run_agrees p m projected checked cut.table (cut.eval_agrees m) result input fuel

theorem returns_iff (value : sortValue m.value out) :
    (lower p projected checked cut result).Returns (model m) input (.cons value .nil) ↔
      ∃ fuel, src.runFrom m fuel entry input = some value :=
  lowerWith_returns_iff p m projected checked cut.table (cut.eval_agrees m) result input value

theorem noFiniteReturn_iff :
    (∀ fuel, (lower p projected checked cut result).run (model m) fuel input = none) ↔
      ∀ fuel, src.runFrom m fuel entry input = none :=
  lowerWith_noFiniteReturn_iff p m projected checked cut.table (cut.eval_agrees m) result input

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.Numbered.DeadProducer
