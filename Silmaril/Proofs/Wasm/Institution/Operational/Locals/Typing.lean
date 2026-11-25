module

public import Silmaril.Wasm.Institution.Operational.Locals.Defs

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.Locals.Proofs

open Silmaril.Semantics.SOS Silmaril.Wasm.Execution.Runtime

private theorem check_append (types stack : List NumType) (a b : List Op) :
    check types stack (a ++ b) = (check types stack a).bind (fun out => check types out b) := by
  induction a generalizing stack with
  | nil => rfl
  | cons op tail ih =>
    cases op with
    | value v => exact ih _
    | get i =>
      simp only [List.cons_append, check]
      cases types[i.toNat]? <;> simp [ih]
    | set i =>
      cases stack with
      | nil => rfl
      | cons t stack =>
        simp only [List.cons_append, check]
        split <;> simp [ih]
    | tee i =>
      cases stack with
      | nil => rfl
      | cons t stack =>
        simp only [List.cons_append, check]
        split <;> simp [ih]

private theorem preserved (a b : State) (h : Edge a b) :
    ∀ stack result, check (a.locals.map Value.type) stack a.code = some result →
      b.locals.map Value.type = a.locals.map Value.type ∧
        check (a.locals.map Value.type) stack b.code = some result := by
  refine Derives.least (M := fun j : Judgment =>
    ∀ stack result, check (j.1.locals.map Value.type) stack j.1.code = some result →
      j.2.locals.map Value.type = j.1.locals.map Value.type ∧
        check (j.1.locals.map Value.type) stack j.2.code = some result) h ?_
  intro r member ih
  change RuleInstance r at member
  cases member with
  | get ls i v found =>
    intro stack result checked
    refine ⟨rfl, ?_⟩
    simpa [check, List.getElem?_map, found] using checked
  | set ls i v bound =>
    intro stack result checked
    change (if (ls.map Value.type)[i.toNat]? = some v.type then
      some stack else none) = some result at checked
    split at checked
    · rename_i sameType
      have mappedBound : i.toNat < (ls.map Value.type).length := by simpa using bound
      have same : (ls.map Value.type)[i.toNat]'mappedBound = v.type :=
        Option.some.inj ((List.getElem?_eq_getElem mappedBound).symm.trans sameType)
      exact ⟨by rw [List.map_set, ← same, List.set_getElem_self], checked⟩
    · contradiction
  | tee ls i v =>
    intro stack result checked
    exact ⟨rfl, by simpa [check] using checked⟩
  | context a b saved tail =>
    intro stack result checked
    change check (a.locals.map Value.type) stack (values saved ++ a.code ++ tail) =
      some result at checked
    simp only [check_append, Option.bind_assoc] at checked
    cases first : check (a.locals.map Value.type) stack (values saved) with
    | none => simp [first] at checked
    | some front =>
      simp only [first, Option.bind_some] at checked
      cases inner : check (a.locals.map Value.type) front a.code with
      | none => simp [inner] at checked
      | some middle =>
        simp only [inner, Option.bind_some] at checked
        obtain ⟨same, h⟩ := ih (a, b) (List.Mem.head _) front middle inner
        refine ⟨same, ?_⟩
        change check (a.locals.map Value.type) stack (values saved ++ b.code ++ tail) =
          some result
        simpa [check_append, Option.bind_assoc, first, h] using checked

theorem closed {a b : State} {types result : List NumType} (guard : Admitted types result a)
    (edge : Edge a b) : Admitted types result b := by
  obtain ⟨same, checked⟩ := guard
  obtain ⟨preserves, remains⟩ := preserved a b edge [] result (same.symm ▸ checked)
  exact ⟨preserves.trans same, same ▸ remains⟩

end Silmaril.Wasm.Institution.Operational.Locals.Proofs
