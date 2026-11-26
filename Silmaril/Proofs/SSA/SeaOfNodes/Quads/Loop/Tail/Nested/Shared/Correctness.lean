module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Defs
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Prefix.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Proofs

open SeaOfNodes.Diamond (Model ValueSort)
open Join (Block)
open Blocks (Bank)

universe u v w

variable {Data : Type u} {Op : SeaOfNodes.Diamond.Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {out : ValueSort Data} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size}
variable (p : Program src entry) (m : Model.{u, v, w} Op)

theorem prefix_bank (old : Bank (regs := regs) m) (occurrence : Occurrence) :
    p.prefixBank m old occurrence = (p.prefixQuads occurrence).eval m old :=
  Prefix.prefix_bank (Prefix.ofProgram p) m old occurrence

theorem suffix_bank (incoming : Bank (regs := regs) m) :
    p.suffixBank m incoming = p.suffix.quads.eval m incoming :=
  Prefix.suffix_bank (Prefix.ofProgram p) m incoming

theorem inner_edges_distinct : p.innerEdgeOccurrence true ≠ p.innerEdgeOccurrence false :=
  Prefix.inner_edges_distinct (Prefix.ofProgram p) (later := p.suffix.blocks ++ p.outerFalse.blocks ++ [p.join, p.latch])
    (by simpa only [Prefix.ofProgram, List.append_assoc] using p.distinct)

theorem run_prefix (old : Bank (regs := regs) m) (fuel : Nat) :
    let occurrence := p.toControl.selected m old
    src.runFrom m (fuel + p.prefixVisits occurrence) p.header old =
      src.runFrom m fuel (p.prefixTarget occurrence) (p.prefixBank m old occurrence) :=
  Prefix.run_prefix (Prefix.ofProgram p) m old fuel

theorem run_suffix (incoming : Bank (regs := regs) m) (fuel : Nat) :
    src.runFrom m (fuel + p.suffix.blocks.length) p.meet incoming =
      src.runFrom m fuel p.join (p.suffixBank m incoming) :=
  Prefix.run_suffix (Prefix.ofProgram p) m incoming fuel

theorem run_to_merge (old : Bank (regs := regs) m) (fuel : Nat) :
    let occurrence := p.toControl.selected m old
    src.runFrom m (fuel + p.mergeVisits occurrence) p.header old =
      src.runFrom m fuel p.join (p.mergeBank m old occurrence) :=
  Prefix.run_to_outer (Prefix.ofProgram p) m old fuel

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Proofs
