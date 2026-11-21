module

public import Silmaril.Formats.Dasl.Named.Defs

public section

namespace Silmaril.Proofs.Formats.Dasl

open Silmaril.Formats.Dasl

variable {Name : Type} {store : Store Name}

theorem expands_of_admitted {tree : Named Name} (admitted : tree.AdmittedBy store) :
    Expands store tree.embed.shallow tree := by
  induction tree with
  | ref impossible => exact impossible.elim
  | obj name target ih =>
    exact .obj (admitted.1 (Or.inl ⟨rfl, rfl⟩)) (ih ⟨fun _ _ hit => admitted.1 (Or.inr hit), admitted.2⟩)
  | blob name bytes => exact .blob (admitted.2 ⟨rfl, rfl⟩)
  | dict keys children ih | list keys children ih =>
    constructor
    intro index
    exact ih index ⟨fun _ _ hit => admitted.1 ⟨index, hit⟩, fun _ _ hit => admitted.2 ⟨index, hit⟩⟩
  | _ => constructor

theorem can_name_of_expands {source : Shallow Name} {tree : Named Name} (expanded : Expands store source tree) :
    CanName store tree.erase source := by
  induction expanded with
  | obj hit _ ih => exact .obj ih hit
  | blob hit => exact .blob hit
  | dict _ ih => exact .dict ih
  | list _ ih => exact .list ih
  | _ => constructor

theorem can_name_lift {value : Value} {source : Shallow Name} (choices : CanName store value source) :
    ∃ tree : Named Name, tree.erase = value ∧ Expands store source tree := by
  classical
  induction choices with
  | obj child hit ih =>
    obtain ⟨tree, erased, expanded⟩ := ih
    exact ⟨.obj _ tree, congrArg Value.obj erased, .obj hit expanded⟩
  | blob hit => exact ⟨.blob _ _, rfl, .blob hit⟩
  | dict _ ih =>
    choose tree erased expanded using ih
    exact ⟨.dict _ tree, congrArg (Tree.dict _) (funext erased), .dict expanded⟩
  | list _ ih =>
    choose tree erased expanded using ih
    exact ⟨.list _ tree, congrArg (Tree.list _) (funext erased), .list expanded⟩
  | _ => exact ⟨_, rfl, by constructor⟩

theorem coherent_iff_no_conflict (tree : Named Name) : tree.Coherent ↔ ¬tree.Conflict := by
  classical
  constructor
  · intro binding conflict
    rcases conflict with ⟨_, _, _, first, second, different⟩ | ⟨_, _, _, first, second, different⟩
    · exact different (binding.1 first second)
    · exact different (binding.2 first second)
  · intro noConflict
    constructor
    · intro name left right first second
      by_contra different
      exact noConflict (.inl ⟨name, left, right, first, second, different⟩)
    · intro name left right first second
      by_contra different
      exact noConflict (.inr ⟨name, left, right, first, second, different⟩)

end Silmaril.Proofs.Formats.Dasl
