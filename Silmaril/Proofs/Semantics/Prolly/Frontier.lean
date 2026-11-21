module

public import Silmaril.Semantics.Prolly.Frontier.Defs
import Silmaril.Semantics.Prolly.Thms

public section

namespace Silmaril.Proofs.Semantics.Prolly.Frontier

open Silmaril.Semantics.Prolly

variable {Key Payload Name Item : Type}

private theorem chunkFrom_map (cut : Nat → Key → Bool) (key : Item → Key)
    (current items : List Item) :
    (chunkFrom (fun count item => cut count (key item)) current items).map (List.map key) =
      chunkFrom cut (current.map key) (items.map key) := by
  induction items generalizing current with
  | nil => cases current <;> simp [chunkFrom]
  | cons head tail ih =>
    by_cases boundary : cut (current.length + 1) (key head) = true <;>
      simp [chunkFrom, boundary, ih]

private theorem lift_keys (groups : List (List (Key × Item))) :
    (lift groups).map Prod.fst = (groups.map (List.map Prod.fst)).filterMap List.getLast? := by
  induction groups with
  | nil => rfl
  | cons group rest ih =>
    cases group with
    | nil => exact ih
    | cons first tail =>
      have lifted : lift ((first :: tail) :: rest) = ((tail.getLastD first).1, first :: tail) :: lift rest := by
        simp [lift]
      rw [lifted, List.map_cons, List.map_cons, List.map_cons, List.filterMap_cons, List.getLast?_cons]
      simp only [← List.getLastD_eq_getLast?, List.getLastD_map, ih]

theorem lift_chunk_keys (policy : Policy Key) (level : Nat) (items : List (Key × Item)) :
    (lift (chunk (fun count pair => policy.cut level count pair.1) items)).map Prod.fst =
      keyStep policy level (items.map Prod.fst) := by
  rw [lift_keys]
  unfold keyStep
  rw [show (chunk _ items).map (List.map Prod.fst) = chunk (policy.cut level) (items.map Prod.fst) from
    chunkFrom_map (policy.cut level) Prod.fst [] items]

theorem grow_level (policy : Policy Key) (fuel level : Nat) (node : Node Key Payload level) :
    (grow policy fuel level node).level = level + (promotions policy fuel level (node.map Prod.fst)).length := by
  induction fuel generalizing level with
  | zero => simp [grow, promotions]
  | succ fuel ih =>
    by_cases within : node.length ≤ policy.width
    · simp [grow, promotions, within]
    · simp [grow, promotions, within, ih, lift_chunk_keys]
      omega

private theorem regroup (address : Block Name Key Payload → Name) (level : Nat)
    (groups : List (Node Key Payload level)) :
    (blockOccurrences address (level + 1) (lift groups)).length =
      (lift groups).length + (blockOccurrences address level groups.flatten).length := by
  induction groups with
  | nil => cases level <;> rfl
  | cons group rest ih =>
    cases group with
    | nil => exact ih
    | cons first tail =>
      cases level <;>
        simp [lift, blockOccurrences, List.flatMap_append] at ih ⊢ <;> omega

theorem grow_occurrences (policy : Policy Key) (address : Block Name Key Payload → Name)
    (fuel level : Nat) (node : Node Key Payload level) :
    (blockOccurrences address (grow policy fuel level node).level (grow policy fuel level node).root).length =
      (blockOccurrences address level node).length +
        ((promotions policy fuel level (node.map Prod.fst)).map List.length).sum := by
  induction fuel generalizing level with
  | zero => simp [grow, promotions]
  | succ fuel ih =>
    by_cases within : node.length ≤ policy.width
    · have step : grow policy (fuel + 1) level node = ⟨level, node⟩ := by simp [grow, within]
      rw [step]
      simp [promotions, within]
    · let groups := chunk (fun count (pair : Key × Content Key Payload level) => policy.cut level count pair.1) node
      have keys := lift_chunk_keys policy level node
      have count := congrArg List.length keys
      simp only [List.length_map] at count
      have step : grow policy (fuel + 1) level node = grow policy fuel (level + 1) (lift groups) := by
        simp [grow, within, groups]
      rw [step]
      simp only [within, ↓reduceIte, promotions, List.length_map, List.map_cons, List.sum_cons]
      change _ = _ + ((keyStep policy level (node.map Prod.fst)).length + _)
      rw [ih (level + 1) (lift groups), regroup, flatten_chunk, keys, count]
      omega

end Silmaril.Proofs.Semantics.Prolly.Frontier
