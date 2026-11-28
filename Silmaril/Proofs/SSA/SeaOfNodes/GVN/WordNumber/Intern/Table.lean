module

public import Silmaril.SSA.SeaOfNodes.GVN.WordNumber.Intern.Defs
import Silmaril.SSA.SeaOfNodes.GVN.WordNumber.Thms

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.GVN.WordNumber.Intern

open Silmaril.SSA.SeaOfNodes.Diamond (Ty)
open Silmaril.SSA.SeaOfNodes.GVN.WordNumber (Key)
open Silmaril.SSA.SeaOfNodes.GVN.WordNumber.Intern

variable {args : List (Ty Unit)} {table after : Table}

theorem intern_spec (table : Table) (signature : Signature) :
    let result := intern table signature
    table <+: result.1 ∧ result.1[result.2]? = some signature ∧
      (table.Nodup → result.1.Nodup) := by
  dsimp only [intern]
  cases found : table.findIdx? (fun existing => decide (existing = signature)) with
  | none =>
    have absent : signature ∉ table := by
      intro member
      have rejected := List.findIdx?_eq_none_iff.mp found signature member
      simp at rejected
    refine ⟨⟨[signature], rfl⟩, by simp, fun unique => ?_⟩
    have distinct : ∀ existing ∈ table, existing ≠ signature :=
      fun _ member same => absent (same ▸ member)
    simpa [List.nodup_append] using And.intro unique distinct
  | some id =>
    obtain ⟨bound, same, _⟩ := List.findIdx?_eq_some_iff_getElem.mp found
    exact ⟨List.prefix_rfl, List.getElem?_eq_some_iff.mpr ⟨bound, of_decide_eq_true same⟩, fun unique => unique⟩

private theorem prefix_lookup (extendsTable : table <+: after) {id : Id} {signature : Signature}
    (found : table[id]? = some signature) : after[id]? = some signature := by
  obtain ⟨suffix, rfl⟩ := extendsTable
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1]
  exact found

theorem decodes_mono {id : Id} {key : Key args} (extendsTable : table <+: after)
    (decoded : Decodes table id key) : Decodes after id key := by
  induction decoded with
  | argument found => exact .argument (prefix_lookup extendsTable found)
  | literal found => exact .literal (prefix_lookup extendsTable found)
  | binary found _ _ ihL ihR => exact .binary (prefix_lookup extendsTable found) ihL ihR

theorem decoded_eq {id : Id} {lhs rhs : Key args}
    (left : Decodes table id lhs) (right : Decodes table id rhs) : lhs = rhs := by
  induction left generalizing rhs with
  | argument found =>
    cases right with
    | argument other =>
      have same := Signature.argument.inj (Option.some.inj (found.symm.trans other))
      exact Key.eq_of_matches (by simp [Key.matches, same])
    | literal other | binary other _ _ => simp [found] at other
  | literal found =>
    cases right with
    | literal other => exact congrArg Key.literal (Signature.literal.inj (Option.some.inj (found.symm.trans other)))
    | argument other | binary other _ _ => simp [found] at other
  | binary found _ _ ihL ihR =>
    cases right with
    | binary other left right =>
      obtain ⟨rfl, rfl, rfl⟩ := Signature.binary.inj (Option.some.inj (found.symm.trans other))
      exact congrArg₂ (Key.binary _) (ihL left) (ihR right)
    | argument other | literal other => simp [found] at other

private theorem id_eq_of_lookup (unique : table.Nodup) {lhs rhs : Id} {signature : Signature}
    (left : table[lhs]? = some signature) (right : table[rhs]? = some signature) : lhs = rhs :=
  unique.eq_of_getElem?_eq (List.getElem?_eq_some_iff.mp left).1 (left.trans right.symm)

theorem id_eq (unique : table.Nodup) {lhs rhs : Id} {key : Key args}
    (left : Decodes table lhs key) (right : Decodes table rhs key) : lhs = rhs := by
  induction left generalizing rhs with
  | argument found =>
    cases right with
    | argument other => exact id_eq_of_lookup unique found other
  | literal found =>
    cases right with
    | literal other => exact id_eq_of_lookup unique found other
  | binary found _ _ ihL ihR =>
    cases right with
    | binary other left right =>
      cases ihL left
      cases ihR right
      exact id_eq_of_lookup unique found other

end Silmaril.Proofs.SSA.SeaOfNodes.GVN.WordNumber.Intern
