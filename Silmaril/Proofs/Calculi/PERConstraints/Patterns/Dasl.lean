module

public import Silmaril.Calculi.PERConstraints.Patterns.Dasl.Defs

@[expose] public section
namespace Silmaril.Calculi.PERConstraints.Patterns.Proofs

open Silmaril.Formats.Dasl

theorem tree_map_surjective {Ref Name NextRef NextName : Type} {refs : Ref → NextRef} {names : Name → NextName}
    (ontoRefs : Function.Surjective refs) (ontoNames : Function.Surjective names) :
    Function.Surjective (Tree.map refs names) := by
  intro tree
  induction tree with
  | ref link => obtain ⟨link', rfl⟩ := ontoRefs link; exact ⟨.ref link', rfl⟩
  | obj name child ih =>
    obtain ⟨name', rfl⟩ := ontoNames name
    obtain ⟨child', rfl⟩ := ih
    exact ⟨.obj name' child', rfl⟩
  | blob name bytes => obtain ⟨name', rfl⟩ := ontoNames name; exact ⟨.blob name' bytes, rfl⟩
  | dict keys children ih =>
    choose preimage renamed using ih
    exact ⟨.dict keys preimage, congrArg (Tree.dict keys) (funext renamed)⟩
  | list len children ih =>
    choose preimage renamed using ih
    exact ⟨.list len preimage, congrArg (Tree.list len) (funext renamed)⟩
  | i64 bits => exact ⟨.i64 bits, rfl⟩
  | bytes value => exact ⟨.bytes value, rfl⟩
  | string value => exact ⟨.string value, rfl⟩
  | bool value => exact ⟨.bool value, rfl⟩
  | null => exact ⟨.null, rfl⟩

end Silmaril.Calculi.PERConstraints.Patterns.Proofs
