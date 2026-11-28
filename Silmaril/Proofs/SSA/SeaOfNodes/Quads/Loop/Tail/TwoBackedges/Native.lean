module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Defs

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Proofs

open Diamond (Model Signature ValueSort sortValue)
open Blocks (Bank)

universe u v w

variable {Data : Type u} {Op : Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {out : ValueSort Data}

theorem source_header (p : Program Op regs out) (m : Model.{u, v, w} Op) (fuel : Nat)
    (old : Bank (regs := regs) m) :
    p.source.runFrom m (fuel + 1) 1 old =
      match p.step m old with
      | .inl result => some result
      | .inr (_, next) => p.source.runFrom m (fuel - 2) 1 next := by
  let current := p.header.eval m old
  have header (n : Nat) : p.source.runFrom m (n + 1) 1 old =
      if (current.get p.again).down then p.source.runFrom m n 2 current else some (current.get p.result) := by
    simp only [Tail.Source.runFrom, show p.source 1 = ⟨p.header, .branch p.again (.jump 2) (.ret p.result)⟩ from rfl,
      Tail.Terminator.select, current]
    by_cases taken : ((p.header.eval m old).get p.again).down = true <;> simp [taken]
  have dispatch (n : Nat) : p.source.runFrom m (n + 1) 2 current =
      p.source.runFrom m n (feedbackBlock (current.get p.select).down) current := by
    simp only [Tail.Source.runFrom, show p.source 2 = ⟨[], .branch p.select
      (.jump (feedbackBlock true)) (.jump (feedbackBlock false))⟩ from rfl,
      Tail.Terminator.select]
    rw [show Join.Block.eval ([] : Join.Block Op regs) m current = current from rfl]
    cases (current.get p.select).down <;> rfl
  have feedback (n : Nat) (side : Bool) :
      p.source.runFrom m (n + 1) (feedbackBlock side) current =
        p.source.runFrom m n 1 ((p.feedback side).eval m current) := by
    cases side <;> rfl
  rw [header]
  change (if (current.get p.again).down then _ else _) =
    match (if (current.get p.again).down then
      Sum.inr ((current.get p.select).down, (p.feedback (current.get p.select).down).eval m current)
      else Sum.inl (current.get p.result)) with
    | .inl result => some result
    | .inr (_, next) => p.source.runFrom m (fuel - 2) 1 next
  by_cases taken : (current.get p.again).down = true
  · simp only [taken, ite_true]
    cases fuel with
    | zero => rfl
    | succ fuel =>
      rw [dispatch]
      cases fuel with
      | zero => rfl
      | succ fuel => exact feedback fuel _
  · simp only [taken]
    rfl

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Proofs
