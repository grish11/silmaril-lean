module

import Silmaril.Semantics.OrderedMap.Transport.Thms
meta import Silmaril.Semantics.OrderedMap.Transport.Thms

open Silmaril.Semantics Silmaril.Semantics.OrderedMap

private def shifted : Nat ↪o Nat := OrderEmbedding.ofStrictMono (· + 10) (by
  intro _ _ ordered
  exact Nat.add_lt_add_right ordered 10)

private def left : OrderedMap Nat Unit := ⟨[(1, ()), (4, ())], by decide⟩
private def right : OrderedMap Nat Unit := ⟨[(2, ()), (4, ())], by decide⟩
private def symmetric : OrderedMap Nat Unit := ⟨[(1, ()), (2, ())], by decide⟩

example (expected : left.combine .union (Overlap.discard (Error := Nat)) right = .ok symmetric) :
    (left.rekey shifted).combine .union (Overlap.discard (Error := Nat)) (right.rekey shifted) =
    .ok (symmetric.rekey shifted) := by
  exact (rekey_combine_iff shifted .union Overlap.discard Overlap.discard (fun _ _ _ => rfl) left right symmetric).mpr expected

public def main : IO Unit := do
  let .ok result := (left.rekey shifted).combine .union (Overlap.discard (Error := Nat)) (right.rekey shifted) |
    throw (IO.userError "shifted symmetric difference")
  unless result.keys == [11, 12] && (result.lookup? 1).isNone && (result.lookup? 11).isSome do
    throw (IO.userError "transport must not add out-of-image keys or change payloads")
