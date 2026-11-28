module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Numbered.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Numbered.Correctness

/-! Exact packet, bounded execution, and finite observations for the original loop. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Numbered

open SeaOfNodes.Diamond (Model Signature Val ValueSort sortValue)
open Join (model)
open Blocks (Bank)
open RVSDG (Tuple)

universe u v w

variable {Data : Type u} {Op : Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {out : ValueSort Data}
variable (p : Program Op regs out) (m : Model.{u, v, w} Op)

/-- One actual activation carries the complete selected feedback bank into
the next header, then returns its full bank with the next test tag. -/
theorem packet_run (fuel : Nat) (bank : Bank (regs := regs) m) :
    (thetaBody p).toGraph.run (model m) fuel bank =
      let next := p.header.eval m ((p.feedback (bank.get p.select).down).eval m bank)
      some (RVSDG.Theta.bodyResult (model m) (next.get p.again).down next) :=
  Proofs.packet_run p m fuel bank

/-- The θ bound counts taken dispatches. Native execution spends three
visits per dispatch, plus entry and the first header. -/
theorem lower_run (fuel : Nat) (input : Bank (regs := regs) m) :
    (lower p).run (model m) fuel input =
      (p.source.runFrom m (3 * fuel + 2) 0 input).map
        (fun value => (Tuple.cons value .nil : Tuple (Val m.value) [.value out])) :=
  Proofs.lower_run p m fuel input

theorem returns_iff (input : Bank (regs := regs) m) (value : sortValue m.value out) :
    (lower p).Returns (model m) input (.cons value .nil) ↔
      ∃ fuel, p.source.runFrom m fuel 0 input = some value :=
  Proofs.returns_iff p m input value

theorem noReturn_iff (input : Bank (regs := regs) m) :
    (∀ fuel, (lower p).run (model m) fuel input = none) ↔
      ¬ ∃ value fuel, p.source.runFrom m fuel 0 input = some value :=
  Proofs.noReturn_iff p m input

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Numbered
