module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Chain.Segment.Incoming.Defs

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Chain.Segment.Proofs

open Diamond (ValueSort Signature Model)
open Blocks (Bank)

universe u v w

variable {Data : Type u} {Op : Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {out : ValueSort Data} {size : Nat}
variable {src : Source Op regs out size} {target site : Fin size}

theorem final_edge (path : Segment src target site) (m : Model.{u, v, w} Op)
    (caller : Fin size) (beforeCaller current : Bank (regs := regs) m)
    (direct : path.blocks = [] →
      (src caller).terminator.select m ((src caller).body.eval m beforeCaller) = .jump site ∧
      (src caller).body.eval m beforeCaller = current) :
    let pred := path.predecessor caller
    let bank := (src pred).body.eval m (path.predecessorBank m beforeCaller current)
    (src pred).terminator.select m bank = .jump target ∧ bank = path.quads.eval m current := by
  induction path generalizing caller beforeCaller current with
  | empty => exact direct rfl
  | jump site edge rest ih =>
    have next := ih site current ((src site).body.eval m current)
      (fun _ => ⟨by rw [edge]; rfl, rfl⟩)
    exact ⟨next.1, next.2.trans List.foldl_append.symm⟩

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Chain.Segment.Proofs
