module

public import Silmaril.Wasm.Institution.Operational.Blocks.Defs

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.Blocks.Proofs

open Silmaril.Semantics.SOS
open Silmaril.Wasm.Execution.Runtime (Value)

private abbrev ValidRule (j : Judgment) : Prop :=
  match j with
  | .body (a, b) => Locals.Edge a b
  | .block a b =>
    (∃ result body, a = .block result body ∧ b = .label result body) ∨
    (∃ result before after, a = .label result before ∧ b = .label result after ∧
      Locals.Edge before after) ∨
    (∃ result ls vs, a = .label result ⟨ls, Locals.values vs⟩ ∧ b = .done ls vs)

theorem invert {a b : State} (step : Edge a b) :
    (∃ result body, a = .block result body ∧ b = .label result body) ∨
    (∃ result before after, a = .label result before ∧ b = .label result after ∧
      Locals.Edge before after) ∨
    (∃ result ls vs, a = .label result ⟨ls, Locals.values vs⟩ ∧ b = .done ls vs) := by
  refine Derives.least (M := ValidRule) step ?_
  intro rule member ih
  change RuleInstance rule at member
  cases member with
  | @body r h => exact .apply h (fun j hj => ih (.body j) (List.mem_map_of_mem hj))
  | enter result body => exact .inl ⟨result, body, rfl, rfl⟩
  | reduce result before after => exact .inr (.inl ⟨result, before, after, rfl, rfl,
      ih (.body (before, after)) (List.Mem.head _)⟩)
  | exit result ls vs => exact .inr (.inr ⟨result, ls, vs, rfl, rfl⟩)

private theorem body_derives {a b : Locals.State} (step : Locals.Edge a b) :
    presentation.Derives (.body (a, b)) := by
  refine Derives.least (M := fun j => presentation.Derives (.body j)) step ?_
  intro r hr ih
  change Locals.RuleInstance r at hr
  refine Derives.apply (RuleInstance.body hr) ?_
  intro j hj
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hj
  exact ih x hx

theorem reduce (result : Option NumType) {a b : Locals.State} (step : Locals.Edge a b) :
    Edge (.label result a) (.label result b) :=
  Derives.apply (RuleInstance.reduce result a b)
    (fun _ h => (List.mem_singleton.mp h).symm ▸ body_derives step)

private theorem check_values (types stack : List NumType) (vs : List Value) :
    Locals.check types stack (Locals.values vs) = some ((vs.map Value.type).reverse ++ stack) := by
  induction vs generalizing stack with
  | nil => rfl
  | cons v tail ih =>
    change Locals.check types (v.type :: stack) (Locals.values tail) = _
    rw [ih]
    simp

theorem closed {types : List NumType} {result : Option NumType} {a b : State}
    (guard : Admitted types result a) (step : Edge a b) : Admitted types result b := by
  rcases invert step with ⟨_, _, rfl, rfl⟩ | ⟨_, _, _, rfl, rfl, edge⟩ |
    ⟨_, _, _, rfl, rfl⟩
  · exact guard
  · exact ⟨guard.1, Locals.closed guard.2 edge⟩
  · obtain ⟨_, same, check⟩ := guard
    rw [check_values] at check
    exact ⟨same, by simpa using check⟩

private theorem contains_local {a b : Locals.State} (edge : Locals.Edge a b) :
    ∃ i, Locals.Op.get i ∈ a.code ∨ Locals.Op.set i ∈ a.code ∨ Locals.Op.tee i ∈ a.code := by
  refine Derives.least (M := fun j : Locals.Judgment =>
    ∃ i, Locals.Op.get i ∈ j.1.code ∨ Locals.Op.set i ∈ j.1.code ∨ Locals.Op.tee i ∈ j.1.code) edge ?_
  intro r hr ih
  change Locals.RuleInstance r at hr
  cases hr with
  | get _ i _ _ => exact ⟨i, .inl (List.Mem.head _)⟩
  | set _ i _ _ => exact ⟨i, .inr (.inl (List.Mem.tail _ (List.Mem.head _)))⟩
  | tee _ i _ => exact ⟨i, .inr (.inr (List.Mem.tail _ (List.Mem.head _)))⟩
  | context a b saved tail =>
    obtain ⟨i, h | h | h⟩ := ih (a, b) (List.Mem.head _) <;> exact ⟨i, by simp [h]⟩

theorem no_values_edge {ls vs : List Value} {out : Locals.State}
    (edge : Locals.Edge ⟨ls, Locals.values vs⟩ out) : False := by
  obtain ⟨i, h | h | h⟩ := contains_local edge <;>
    obtain ⟨v, _, eq⟩ := List.mem_map.mp h <;> cases eq

end Silmaril.Wasm.Institution.Operational.Blocks.Proofs
