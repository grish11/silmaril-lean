module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Chain.Segment.Defs

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Chain.Segment.Proofs

open Diamond (ValueSort Signature Model sortValue)
open Join (Block)
open Blocks (Bank)

universe u v w

variable {Data : Type u} {Op : Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {out : ValueSort Data} {size : Nat}
variable {src : Source Op regs out size} {target site : Fin size}

theorem run_segment (path : Segment src target site) (m : Model.{u, v, w} Op)
    (fuel : Nat) (old : Bank (regs := regs) m) :
    src.runFrom m (fuel + path.blocks.length) site old =
      src.runFrom m fuel target (path.quads.eval m old) := by
  induction path generalizing old with
  | empty => simp [Segment.blocks, Segment.quads, Block.eval]
  | jump site edge rest ih =>
    simp only [Segment.blocks, List.length_cons, Nat.add_succ, Source.runFrom, edge,
      Terminator.select, Segment.quads, Block.eval, List.foldl_append]
    exact ih ((src site).body.eval m old)

theorem run_short (path : Segment src target site) (m : Model.{u, v, w} Op)
    (fuel : Nat) (old : Bank (regs := regs) m)
    (short : fuel < path.blocks.length) : src.runFrom m fuel site old = none := by
  induction path generalizing fuel old with
  | empty => simp [Segment.blocks] at short
  | jump site edge rest ih =>
    cases fuel with
    | zero => rfl
    | succ fuel =>
      simp only [Source.runFrom, edge, Terminator.select]
      exact ih fuel ((src site).body.eval m old) (by simpa [Segment.blocks] using short)

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Chain.Segment.Proofs
