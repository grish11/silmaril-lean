module

public import Silmaril.Semantics.Prolly.Bounds.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset

public section

namespace Silmaril.Proofs.Semantics.Prolly.Bounds

open Silmaril.Semantics.Prolly
open scoped BigOperators

variable {Sample Key : Type}

private theorem scanCount (policy : Policy Key) (level : Nat) (current keys : List Key) :
    policy.width * (chunkFrom (policy.cut level) current keys).length ≤
      current.length + keys.length + policy.width * (keys.countP (policy.bucket level)) + policy.width := by
  induction keys generalizing current with
  | nil => cases current <;> simp [chunkFrom]
  | cons head tail ih =>
    by_cases cuts : policy.cut level (current.length + 1) head = true
    · have rest := ih []
      by_cases forced : policy.width ≤ current.length + 1
      · by_cases hit : policy.bucket level head = true <;>
          simp [chunkFrom, cuts, hit, Nat.mul_succ] at rest ⊢ <;> omega
      · have hit : policy.bucket level head = true := by
          simp [Policy.cut, forced] at cuts
          exact cuts.2
        simp [chunkFrom, cuts, hit, Nat.mul_succ] at rest ⊢
        omega
    · have rest := ih (current ++ [head])
      by_cases hit : policy.bucket level head = true <;>
        simp [chunkFrom, cuts, hit, Nat.mul_succ] at rest ⊢ <;> omega

theorem chunk_count (policy : Policy Key) (level : Nat) (keys : List Key) :
    policy.width * (chunk (policy.cut level) keys).length ≤
      keys.length + policy.width * (keys.countP (policy.bucket level)) + policy.width := by
  simpa [chunk] using scanCount policy level [] keys

private theorem sum_hits [Fintype Sample] (model : UniformBuckets Sample Key) (level : Nat) (keys : List Key) :
    (∑ sample : Sample, keys.countP (model.hit sample level)) = (keys.map (model.hits level)).sum := by
  induction keys with
  | nil => simp
  | cons head tail ih =>
    have indicator : (∑ sample : Sample, (if model.hit sample level head then 1 else 0 : Nat)) =
        model.hits level head := by
      rw [UniformBuckets.hits, ← Finset.sum_filter]
      simp
    simp only [List.countP_cons, List.map_cons, List.sum_cons, ← indicator, ← ih, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro sample _
    cases model.hit sample level head <;> simp [Nat.add_comm]

theorem uniform_chunk_bound [Fintype Sample] (model : UniformBuckets Sample Key) (level : Nat)
    (keys : List Key) (cap : Nat) (marginal : ∀ key ∈ keys, model.hits level key ≤ cap) :
    (∑ sample : Sample, model.width * model.chunks sample level keys) ≤
      Fintype.card Sample * (keys.length + model.width) + model.width * (keys.length * cap) := by
  calc
    _ ≤ ∑ sample : Sample, (keys.length + model.width + model.width * keys.countP (model.hit sample level)) := by
      apply Finset.sum_le_sum
      intro sample _
      simpa [UniformBuckets.chunks, UniformBuckets.policy, Nat.add_right_comm] using
        chunk_count (model.policy sample) level keys
    _ = Fintype.card Sample * (keys.length + model.width) + model.width * (keys.map (model.hits level)).sum := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, sum_hits]
      simp
    _ ≤ _ := by
      apply Nat.add_le_add_left
      apply Nat.mul_le_mul_left
      induction keys with
      | nil => simp
      | cons head tail ih =>
        have headBound := marginal head (by simp)
        have tailBound := ih (fun item hit => marginal item (List.mem_cons_of_mem _ hit))
        simp [Nat.succ_mul]
        omega

end Silmaril.Proofs.Semantics.Prolly.Bounds
