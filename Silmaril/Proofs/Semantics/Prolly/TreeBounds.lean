module

public import Silmaril.Semantics.Prolly.Bounds.Tree.Defs
import Silmaril.Semantics.Prolly.Bounds.Thms
import Silmaril.Semantics.Prolly.Frontier.Thms
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset

public section

namespace Silmaril.Proofs.Semantics.Prolly.TreeBounds

open Silmaril.Semantics Silmaril.Semantics.Prolly
open scoped BigOperators

variable {Sample Key Payload Name : Type}

private theorem frontier_succ (policy : Policy Key) (steps level : Nat) (keys : List Key) :
    frontierAt policy (steps + 1) level keys =
      keyStep policy (level + steps) (activeKeys policy (frontierAt policy steps level keys)) := by
  induction steps generalizing level keys with
  | zero => rfl
  | succ steps ih =>
    change frontierAt policy (steps + 1) (level + 1) (keyStep policy level (activeKeys policy keys)) = _
    rw [ih, show level + 1 + steps = level + (steps + 1) by omega]
    rfl

private theorem frontier_nil (policy : Policy Key) (steps level : Nat) :
    frontierAt policy steps level [] = [] := by
  induction steps generalizing level with
  | zero => rfl
  | succ steps ih => simp [frontierAt, activeKeys, keyStep, chunk, chunkFrom, ih]

private theorem promotions_sum (policy : Policy Key) (fuel level : Nat) (keys : List Key) :
    ((promotions policy fuel level keys).map List.length).sum =
      ∑ step ∈ Finset.range fuel, (frontierAt policy (step + 1) level keys).length := by
  induction fuel generalizing level keys with
  | zero => simp [promotions]
  | succ fuel ih =>
    rw [Finset.sum_range_succ']
    by_cases fits : keys.length ≤ policy.width
    · simp [promotions, fits, frontierAt, activeKeys, keyStep, chunk, chunkFrom, frontier_nil]
    · simp only [promotions, fits, ↓reduceIte, List.map_cons, List.sum_cons, ih, frontierAt, activeKeys]
      exact Nat.add_comm _ _

private theorem wide_of_lt_promotions (policy : Policy Key) (fuel level step : Nat) (keys : List Key)
    (deep : step < (promotions policy fuel level keys).length) :
    policy.width < (frontierAt policy step level keys).length := by
  induction fuel generalizing level step keys with
  | zero => simp [promotions] at deep
  | succ fuel ih =>
    by_cases fits : keys.length ≤ policy.width
    · simp [promotions, fits] at deep
    · cases step with
      | zero => exact Nat.lt_of_not_ge fits
      | succ step =>
        simp only [promotions, fits, ↓reduceIte, List.length_cons, Nat.succ_lt_succ_iff] at deep
        simpa [frontierAt, activeKeys, fits] using ih (level + 1) step (keyStep policy level keys) deep

theorem mass_succ [Fintype Sample] [DecidableEq Key] {model : UniformBuckets Sample Key}
    {keys : List Key} {numerator denominator : Nat} (cap : model.FrontierCap keys numerator denominator) (steps : Nat) :
    (denominator * model.width) * model.frontierMass keys (steps + 1) ≤
      (2 * denominator + model.width * numerator) * model.frontierMass keys steps := by
  let select sample := activeKeys (model.policy sample) (frontierAt (model.policy sample) steps 0 keys)
  have next sample : frontierAt (model.policy sample) (steps + 1) 0 keys =
      keyStep (model.policy sample) steps (select sample) := by simp [frontier_succ, select]
  have cost (sample : Sample) :
      (select sample).length + (if (select sample).isEmpty then 0 else model.width) ≤
        2 * (frontierAt (model.policy sample) steps 0 keys).length := by
    unfold select activeKeys
    split
    · simp
    · rename_i wide
      change ¬ (frontierAt (model.policy sample) steps 0 keys).length ≤ model.width at wide
      have charge : (if (frontierAt (model.policy sample) steps 0 keys).isEmpty then 0 else model.width) ≤
          model.width := by split <;> simp
      omega
  have size (sample : Sample) :
      (select sample).length ≤ (frontierAt (model.policy sample) steps 0 keys).length := by
    unfold select activeKeys
    split <;> simp
  calc
    _ ≤ denominator * (∑ sample : Sample, model.width * model.chunks sample steps (select sample)) := by
      unfold UniformBuckets.frontierMass
      rw [Nat.mul_assoc, Finset.mul_sum]
      exact Nat.mul_le_mul_left _ (Finset.sum_le_sum fun sample _ => by
        rw [next]
        exact Nat.mul_le_mul_left _ (keyStep_length_le _ _ _))
    _ ≤ _ := (uniform_adaptive_chunk_bound_active (cap steps)).trans (by
      have costBound := Finset.sum_le_sum (fun sample (_ : sample ∈ Finset.univ) => cost sample)
      have sizeBound := Finset.sum_le_sum (fun sample (_ : sample ∈ Finset.univ) => size sample)
      rw [← Finset.mul_sum] at costBound
      refine (Nat.add_le_add (Nat.mul_le_mul_left denominator costBound)
        (Nat.mul_le_mul_left model.width (Nat.mul_le_mul_left numerator sizeBound))).trans_eq ?_
      rw [UniformBuckets.frontierMass, Nat.add_mul, Nat.mul_assoc, Nat.mul_left_comm denominator 2,
        Nat.mul_assoc model.width])

private theorem mass_iterate [Fintype Sample] [DecidableEq Key] {model : UniformBuckets Sample Key}
    {keys : List Key} {numerator denominator : Nat} (cap : model.FrontierCap keys numerator denominator) (steps : Nat) :
    (denominator * model.width)^steps * model.frontierMass keys steps ≤
      (2 * denominator + model.width * numerator)^steps * model.frontierMass keys 0 := by
  let scale := denominator * model.width
  let coeff := 2 * denominator + model.width * numerator
  induction steps with
  | zero => exact Nat.le_refl _
  | succ steps ih =>
    calc
      _ = scale^steps * (scale * model.frontierMass keys (steps + 1)) := by rw [Nat.pow_succ, Nat.mul_assoc]
      _ ≤ scale^steps * (coeff * model.frontierMass keys steps) := Nat.mul_le_mul_left _ (mass_succ cap steps)
      _ = coeff * (scale^steps * model.frontierMass keys steps) := by ac_rfl
      _ ≤ coeff * (coeff^steps * model.frontierMass keys 0) := Nat.mul_le_mul_left _ ih
      _ = _ := by rw [Nat.pow_succ, Nat.mul_assoc, Nat.mul_left_comm coeff]

private theorem sum_shift_le (mass : Nat → Nat) (fuel : Nat) :
    (∑ step ∈ Finset.range fuel, mass step) ≤ mass 0 + ∑ step ∈ Finset.range fuel, mass (step + 1) := by
  induction fuel with
  | zero => simp
  | succ fuel _ =>
    rw [Finset.sum_range_succ', Finset.sum_range_succ]
    omega

private theorem sum_mass [Fintype Sample] [DecidableEq Key] {model : UniformBuckets Sample Key}
    {keys : List Key} {numerator denominator : Nat} (cap : model.FrontierCap keys numerator denominator)
    (fuel : Nat) (contract : 2 * denominator + model.width * numerator < denominator * model.width) :
    (denominator * model.width - (2 * denominator + model.width * numerator)) *
        (∑ step ∈ Finset.range fuel, model.frontierMass keys (step + 1)) ≤
      (2 * denominator + model.width * numerator) * model.frontierMass keys 0 := by
  let scale := denominator * model.width
  let coeff := 2 * denominator + model.width * numerator
  let total := ∑ step ∈ Finset.range fuel, model.frontierMass keys (step + 1)
  have bound : scale * total ≤ coeff * (model.frontierMass keys 0 + total) := by
    calc
      _ ≤ coeff * ∑ step ∈ Finset.range fuel, model.frontierMass keys step := by
        simp only [total, Finset.mul_sum]
        exact Finset.sum_le_sum (fun step _ => mass_succ cap step)
      _ ≤ _ := Nat.mul_le_mul_left _ (sum_shift_le _ _)
  have split := Nat.sub_add_cancel (Nat.le_of_lt contract)
  change scale - coeff + coeff = scale at split
  change (scale - coeff) * total ≤ coeff * model.frontierMass keys 0
  rw [← split, Nat.add_mul, Nat.mul_add] at bound
  omega

theorem build_occurrences [Fintype Sample] [LinearOrder Key] {model : UniformBuckets Sample Key}
    {map : OrderedMap Key Payload} {numerator denominator : Nat}
    (cap : model.FrontierCap (map.entries.map Prod.fst) numerator denominator)
    (contract : 2 * denominator + model.width * numerator < denominator * model.width)
    (address : Sample → Block Name Key Payload → Name) :
    (denominator * model.width - (2 * denominator + model.width * numerator)) *
        (∑ sample : Sample, let tree := build (model.policy sample) map
                            (blockOccurrences (address sample) tree.level tree.root).length - 1) ≤
      (2 * denominator + model.width * numerator) * (Fintype.card Sample * map.entries.length) := by
  simp only [build_occurrences_eq_promotions, Nat.add_sub_cancel_left, promotions_sum]
  rw [Finset.sum_comm]
  simpa [UniformBuckets.frontierMass, frontierAt, Finset.sum_const, nsmul_eq_mul] using
    sum_mass cap map.entries.length contract

theorem build_depth_tail [Fintype Sample] [LinearOrder Key] {model : UniformBuckets Sample Key}
    {map : OrderedMap Key Payload} {numerator denominator : Nat}
    (cap : model.FrontierCap (map.entries.map Prod.fst) numerator denominator) (steps : Nat) :
    (denominator * model.width)^steps *
        ((model.width + 1) * (Finset.univ.filter fun sample : Sample => steps < (build (model.policy sample) map).level).card) ≤
      (2 * denominator + model.width * numerator)^steps * (Fintype.card Sample * map.entries.length) := by
  have eventBound : (model.width + 1) *
      (Finset.univ.filter fun sample : Sample => steps < (build (model.policy sample) map).level).card ≤
        model.frontierMass (map.entries.map Prod.fst) steps := by
    have counted : (∑ _sample ∈ Finset.univ.filter fun sample : Sample => steps < (build (model.policy sample) map).level,
        (model.width + 1)) = (model.width + 1) *
          (Finset.univ.filter fun sample : Sample => steps < (build (model.policy sample) map).level).card := by
      simp [Finset.sum_const, nsmul_eq_mul, Nat.mul_comm]
    rw [UniformBuckets.frontierMass, ← counted, Finset.sum_filter]
    apply Finset.sum_le_sum
    intro sample _
    split
    · rename_i deep
      rw [build_level_eq_promotions] at deep
      exact wide_of_lt_promotions (model.policy sample) map.entries.length 0 steps _ deep
    · exact Nat.zero_le _
  exact (Nat.mul_le_mul_left _ eventBound).trans (by
    simpa [UniformBuckets.frontierMass, frontierAt, Finset.sum_const, nsmul_eq_mul] using mass_iterate cap steps)

end Silmaril.Proofs.Semantics.Prolly.TreeBounds
