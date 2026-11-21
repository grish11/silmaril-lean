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

private theorem pool_sum_hits (pool : Finset Sample) (model : UniformBuckets Sample Key) (level : Nat) (keys : List Key) :
    (∑ sample ∈ pool, keys.countP (model.hit sample level)) =
      (keys.map fun key => (pool.filter fun sample => model.hit sample level key = true).card).sum := by
  induction keys with
  | nil => simp
  | cons head tail ih =>
    have indicator : (∑ sample ∈ pool, (if model.hit sample level head then 1 else 0 : Nat)) =
        (pool.filter fun sample => model.hit sample level head = true).card := by
      rw [← Finset.sum_filter]
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
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, pool_sum_hits]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rfl
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

private theorem fiber_hits [Fintype Sample] [DecidableEq Key] {model : UniformBuckets Sample Key}
    {level : Nat} {select : Sample → List Key} {numerator denominator : Nat}
    (cap : model.ConditionalCap level select numerator denominator) (keys : List Key) :
    denominator * (∑ sample ∈ selectionFiber select keys, (select sample).countP (model.hit sample level)) ≤
      numerator * (∑ sample ∈ selectionFiber select keys, (select sample).length) := by
  let pool := selectionFiber select keys
  have picks : ∀ sample ∈ pool, select sample = keys := fun _ hit => (Finset.mem_filter.mp hit).2
  have counts : (∑ sample ∈ pool, (select sample).countP (model.hit sample level)) =
      ∑ sample ∈ pool, keys.countP (model.hit sample level) :=
    Finset.sum_congr rfl fun sample hit => by rw [picks sample hit]
  have lengths : (∑ sample ∈ pool, (select sample).length) = ∑ _sample ∈ pool, keys.length :=
    Finset.sum_congr rfl fun sample hit => by rw [picks sample hit]
  change denominator * (∑ sample ∈ pool, _) ≤ numerator * (∑ sample ∈ pool, _)
  rw [counts, lengths, pool_sum_hits]
  let hits (key : Key) := (pool.filter fun sample => model.hit sample level key = true).card
  have marginal : ∀ key ∈ keys, denominator * hits key ≤ numerator * pool.card := cap.2 keys
  have sumLe (items : List Key) (pointwise : ∀ key ∈ items, denominator * hits key ≤ numerator * pool.card) :
      denominator * (items.map hits).sum ≤ items.length * (numerator * pool.card) := by
    induction items with
    | nil => simp
    | cons head tail ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.mul_add, Nat.add_mul, Nat.one_mul]
      rw [Nat.add_comm (tail.length * (numerator * pool.card))]
      exact Nat.add_le_add (pointwise _ (by simp)) (ih fun key hit => pointwise key (List.mem_cons_of_mem _ hit))
  simpa [hits, Finset.sum_const, nsmul_eq_mul, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using sumLe keys marginal

theorem adaptive_chunk_bound_active [Fintype Sample] [DecidableEq Key] {model : UniformBuckets Sample Key}
    {level : Nat} {select : Sample → List Key} {numerator denominator : Nat}
    (cap : model.ConditionalCap level select numerator denominator) :
    denominator * (∑ sample : Sample, model.width * model.chunks sample level (select sample)) ≤
      denominator * (∑ sample : Sample, ((select sample).length + if (select sample).isEmpty then 0 else model.width)) +
        model.width * (numerator * ∑ sample : Sample, (select sample).length) := by
  let support := (Finset.univ : Finset Sample).image select
  have covered : ∀ sample ∈ (Finset.univ : Finset Sample), select sample ∈ support :=
    fun _ present => Finset.mem_image_of_mem select present
  let sampleHits (sample : Sample) := (select sample).countP (model.hit sample level)
  let sampleLength (sample : Sample) := (select sample).length
  let fixedCost (sample : Sample) := if (select sample).isEmpty then 0 else model.width
  have scaledHits : denominator * (∑ sample : Sample, sampleHits sample) ≤
      numerator * ∑ sample : Sample, sampleLength sample := by
    rw [← Finset.sum_fiberwise_of_maps_to covered sampleHits, ← Finset.sum_fiberwise_of_maps_to covered sampleLength,
      Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_le_sum fun keys _ => fiber_hits cap keys
  calc
    _ ≤ denominator * (∑ sample : Sample, (sampleLength sample + fixedCost sample + model.width * sampleHits sample)) := by
      apply Nat.mul_le_mul_left
      apply Finset.sum_le_sum
      intro sample _
      cases chosen : select sample with
      | nil => simp [chosen, UniformBuckets.chunks, chunk, chunkFrom, fixedCost, sampleLength, sampleHits]
      | cons head tail =>
        simpa [chosen, UniformBuckets.chunks, UniformBuckets.policy, fixedCost, sampleHits, sampleLength,
          Nat.add_right_comm] using chunk_count (model.policy sample) level (select sample)
    _ = denominator * (∑ sample : Sample, (sampleLength sample + fixedCost sample)) +
        model.width * (denominator * ∑ sample : Sample, sampleHits sample) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, Nat.mul_add, Nat.mul_left_comm denominator model.width]
    _ ≤ _ := Nat.add_le_add_left (Nat.mul_le_mul_left model.width scaledHits) _

theorem adaptive_chunk_bound [Fintype Sample] [DecidableEq Key] {model : UniformBuckets Sample Key}
    {level : Nat} {select : Sample → List Key} {numerator denominator : Nat}
    (cap : model.ConditionalCap level select numerator denominator) :
    denominator * (∑ sample : Sample, model.width * model.chunks sample level (select sample)) ≤
      denominator * (∑ sample : Sample, ((select sample).length + model.width)) +
        model.width * (numerator * ∑ sample : Sample, (select sample).length) := by
  refine (adaptive_chunk_bound_active cap).trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ ?_) _)
  exact Finset.sum_le_sum fun sample _ => Nat.add_le_add_left (by split <;> simp) _

end Silmaril.Proofs.Semantics.Prolly.Bounds
