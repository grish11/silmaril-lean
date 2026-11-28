module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Chain.Segment.Incoming.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Correctness
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Prefix.Thms

/-! # Exact packets and source visits through outer reconvergence -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer

open SeaOfNodes.Diamond (Model ValueSort)
open Blocks (Bank)

universe u v w

variable {Data : Type u} {Op : SeaOfNodes.Diamond.Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {out : ValueSort Data} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size}
variable (p : Program src entry) (m : Model.{u, v, w} Op)

/-- The two columns remain distinct even when both transfers are direct. -/
theorem Program.inner_edges_distinct : p.innerEdgeOccurrence true ≠ p.innerEdgeOccurrence false :=
  Proofs.inner_edges_distinct p

/-- The exclusive outer routes contribute distinct predecessor occurrences. -/
theorem Program.outer_edges_distinct : p.outerEdgeOccurrence true ≠ p.outerEdgeOccurrence false :=
  Proofs.outer_edges_distinct p

theorem Program.outer_predecessors_distinct :
    (p.outerEdgeOccurrence true).1 ≠ (p.outerEdgeOccurrence false).1 :=
  Proofs.outer_predecessors_distinct p

/-- The original last predecessor takes the selected edge to the outer
tail and supplies its source-computed full bank. -/
theorem Program.selected_outer_edge (old : Bank (regs := regs) m) :
    let occurrence := p.toControl.selected m old
    let pred := (p.outerEdgeOccurrence (occurrence != .outerFalse)).1
    let bank := (src pred).body.eval m (p.outerPredecessorBank m old occurrence)
    (src pred).terminator.select m bank = .jump p.stop ∧ bank = p.outerBank m old occurrence :=
  Proofs.selected_outer_edge p m old

/-- The selected outer predecessor supplies the complete reaching bank
before the common tail. -/
theorem Program.run_to_outer (old : Bank (regs := regs) m) (fuel : Nat) :
    let occurrence := p.toControl.selected m old
    src.runFrom m (fuel + p.outerVisits occurrence) p.header old =
      src.runFrom m fuel p.stop (p.outerBank m old occurrence) :=
  Prefix.run_to_outer p.toRoutes m old fuel

/-- All final suffix wires read the selected outer bank through the
ordered quad compiler. -/
theorem Program.outer_suffix_bank (incoming : Bank (regs := regs) m) :
    p.outerSuffixBank m incoming = p.outerSuffix.quads.eval m incoming :=
  Proofs.outer_suffix_bank p m incoming

theorem Program.run_outer_suffix (incoming : Bank (regs := regs) m) (fuel : Nat) :
    src.runFrom m (fuel + p.outerSuffix.blocks.length) p.stop incoming =
      src.runFrom m fuel p.join (p.outerSuffixBank m incoming) :=
  Proofs.run_outer_suffix p m incoming fuel

/-- Resume the original source at the common merge with the exact bank
and remaining budget after the chosen prefix and any shared visits. -/
theorem Program.run_to_merge (old : Bank (regs := regs) m) (fuel : Nat) :
    let occurrence := p.toControl.selected m old
    src.runFrom m (fuel + p.mergeVisits occurrence) p.header old =
      src.runFrom m fuel p.join (p.mergeBank m old occurrence) :=
  Proofs.run_to_merge p m old fuel

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer
