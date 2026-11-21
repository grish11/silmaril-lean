module

import Silmaril.Semantics.Prolly.Bounds.Thms
import Mathlib.Data.Fintype.BigOperators
meta import Silmaril.Semantics.Prolly.Bounds.Defs

open Silmaril.Semantics.Prolly

private def model : UniformBuckets Bool Nat := ⟨4, by decide, fun sample _ _ => sample⟩

example (level : Nat) (keys : List Nat) :
    4 * model.chunks false level keys + 4 * model.chunks true level keys ≤
      2 * (keys.length + 4) + 4 * keys.length := by
  have bound := uniform_chunk_bound model level keys 1 (fun _ _ => by
    change model.hits 0 0 ≤ 1
    decide)
  simpa [model, Fintype.card_bool, Fintype.sum_bool, Nat.add_comm] using bound

private def selected (sample : Bool) : List Bool := [sample, sample, !sample]
private def correlated : UniformBuckets Bool Bool := ⟨4, by decide, fun sample _ key => sample == key⟩

example (key : Bool) : correlated.hits 0 key = 1 := by cases key <;> decide

example : ¬ correlated.ConditionalCap 0 selected 1 2 := by
  intro cap
  have impossible : (2 : Nat) ≤ 1 := cap.2 [false, false, true] false (by simp)
  exact (by decide : ¬ (2 : Nat) ≤ 1) impossible

public def main : IO Unit := do
  let keys := [0, 1, 2, 3, 4]
  unless model.chunks false 0 keys = 2 ∧ model.chunks true 0 keys = 3 do
    throw (IO.userError "width-only and bucket cuts must differ in the shared-draw model")
