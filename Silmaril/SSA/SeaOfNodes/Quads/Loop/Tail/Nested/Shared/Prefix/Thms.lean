module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Prefix.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Prefix.Correctness

/-! # Exact visits and γ packets through a checked routing prefix -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Prefix

open SeaOfNodes.Diamond (Model Ty Val ValueSort dataPorts)
open RVSDG (Locals Tuple Wires extend)
open RVSDG.NestedTheta (Term)
open Join (Opcode model)
open Join.Finite (Plan)
open Nested.Numbered (splitSigs)
open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond (thenBase)
open Join (Block)
open Blocks (Bank)

universe u v w

variable {Data : Type u} {Op : SeaOfNodes.Diamond.Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {out : ValueSort Data} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size}

variable (p : Routes src entry) (m : Model.{u, v, w} Op)

theorem compiled_bank (quads : Block Op regs) (old : Bank (regs := regs) m) :
    let compiled := CFG.compileBlock quads (initial regs)
    compiled.outgoing.read old (compiled.flow.eval m old PUnit.unit) = quads.eval m old :=
  Proofs.compiled_bank m quads old

theorem predecessor_mem {target site : Fin size}
    (segment : Chain.Segment src target site) (caller : Fin size) :
    (segment.blocks = [] ∧ segment.predecessor caller = caller) ∨
      segment.predecessor caller ∈ segment.blocks :=
  Proofs.predecessor_mem segment caller

theorem inner_edges_distinct {later : List (Fin size)}
    (ordered : ([entry, p.header, p.inner] ++ p.innerTrue.blocks ++ p.innerFalse.blocks ++ later).Nodup) :
    p.innerEdgeOccurrence true ≠ p.innerEdgeOccurrence false :=
  Proofs.inner_edges_distinct p ordered

theorem prefix_bank (old : Bank (regs := regs) m) (occurrence : Occurrence) :
    p.prefixBank m old occurrence = (p.prefixQuads occurrence).eval m old :=
  Proofs.prefix_bank p m old occurrence

theorem suffix_bank (incoming : Bank (regs := regs) m) :
    p.suffixBank m incoming = p.suffix.quads.eval m incoming :=
  Proofs.suffix_bank p m incoming

theorem run_prefix (old : Bank (regs := regs) m) (fuel : Nat) :
    let occurrence := p.toControl.selected m old
    src.runFrom m (fuel + p.prefixVisits occurrence) p.header old =
      src.runFrom m fuel (p.prefixTarget occurrence) (p.prefixBank m old occurrence) :=
  Proofs.run_prefix p m old fuel

theorem run_suffix (incoming : Bank (regs := regs) m) (fuel : Nat) :
    src.runFrom m (fuel + p.suffix.blocks.length) p.meet incoming =
      src.runFrom m fuel p.stop (p.suffixBank m incoming) :=
  Proofs.run_suffix p m incoming fuel

theorem run_to_outer (old : Bank (regs := regs) m) (fuel : Nat) :
    let occurrence := p.toControl.selected m old
    src.runFrom m (fuel + p.outerVisits occurrence) p.header old =
      src.runFrom m fuel p.stop (p.outerBank m old occurrence) :=
  Proofs.run_to_outer p m old fuel

theorem afterHeader_run {results : List (Ty Data)} {suffix : List (List (Ty Data))}
    (finish : Wires (dataPorts regs)
        (extend (extend [] (src p.header).body.producers) (splitSigs regs)) (dataPorts regs) →
      Term (Opcode Op) (dataPorts regs)
        (extend (extend [] (src p.header).body.producers) (splitSigs regs)) suffix results)
    (fuel : Nat) (old : Bank (regs := regs) m) (observe : Bank (regs := regs) m → Option (Tuple (Val m.value) results))
    (agrees : ∀ wires locals, (finish wires).eval (model m) fuel old locals = observe (wires.read old locals)) :
    (afterHeader p finish).run (model m) fuel old =
      observe (p.outerBank m old (p.toControl.selected m old)) :=
  Proofs.afterHeader_run p m finish fuel old observe agrees

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Prefix
