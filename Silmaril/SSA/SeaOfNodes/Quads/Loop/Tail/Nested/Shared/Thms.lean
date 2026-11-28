module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Correctness

/-! # Exact packets and source visits through the common inner suffix -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared

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

/-- Reading the selected prefix transfer gives the final bank of its
ordered source assignments. -/
theorem Program.prefix_bank (old : Bank (regs := regs) m) (occurrence : Occurrence) :
    p.prefixBank m old occurrence = (p.prefixQuads occurrence).eval m old :=
  Proofs.prefix_bank p m old occurrence

/-- The shared transfer reads the ordered suffix's final bank. -/
theorem Program.suffix_bank (incoming : Bank (regs := regs) m) :
    p.suffixBank m incoming = p.suffix.quads.eval m incoming :=
  Proofs.suffix_bank p m incoming

/-- The selected predecessor delivers its complete compiled bank. For
an inner edge the target is the reconvergence. The outer false edge
instead goes to the original common merge with its own bank. -/
theorem Program.run_prefix (old : Bank (regs := regs) m) (fuel : Nat) :
    let occurrence := p.toControl.selected m old
    src.runFrom m (fuel + p.prefixVisits occurrence) p.header old =
      src.runFrom m fuel (p.prefixTarget occurrence) (p.prefixBank m old occurrence) :=
  Proofs.run_prefix p m old fuel

/-- Every checked shared block executes once on the selected full bank.
The compiled suffix packet becomes the input to the original merge. -/
theorem Program.run_suffix (incoming : Bank (regs := regs) m) (fuel : Nat) :
    src.runFrom m (fuel + p.suffix.blocks.length) p.meet incoming =
      src.runFrom m fuel p.join (p.suffixBank m incoming) :=
  Proofs.run_suffix p m incoming fuel

/-- Resume the original source at the common merge with the exact bank
and remaining budget after the chosen prefix and any shared visits. -/
theorem Program.run_to_merge (old : Bank (regs := regs) m) (fuel : Nat) :
    let occurrence := p.toControl.selected m old
    src.runFrom m (fuel + p.mergeVisits occurrence) p.header old =
      src.runFrom m fuel p.join (p.mergeBank m old occurrence) :=
  Proofs.run_to_merge p m old fuel

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared
