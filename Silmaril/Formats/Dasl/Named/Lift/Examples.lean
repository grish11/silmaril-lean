module

import Silmaril.Formats.Dasl.Named.Lift.Thms

namespace Silmaril.Formats.Dasl

open Silmaril.Semantics.Naming

private def payload : ByteArray := ByteArray.empty

private def policy : Store Bool :=
  ⟨nameGraph fun _ => some true, nameGraph fun _ => some false⟩

private def objects (name : Bool) : Option (Shallow Bool) :=
  if name then some (.ref (.blob false)) else none

private def blobs (name : Bool) : Option ByteArray := if name then none else some payload

private def available : Store Bool := ⟨graph objects, graph blobs⟩

private theorem available_binding : available.Binding := ⟨graph_binding _, graph_binding _⟩

private def nested : Value := .obj (.blob payload)

private theorem nested_coverage : nested.NamingCoverage (available.selectedBy policy) := by
  refine ⟨⟨false, rfl, rfl⟩, ?_⟩
  intro _ child
  cases child with
  | blob hit =>
    cases Option.some.inj hit.1
    exact ⟨true, rfl, rfl⟩

example : ∃ tree : Named Bool, tree.erase = nested ∧ tree.AdmittedBy policy ∧ tree.Compatible available :=
  nested_coverage.lift_selected available_binding

example : ¬ policy.Binding := by
  intro bound
  have equal : (.null : Shallow Bool) = .bool false := bound.1 (name := true) rfl rfl
  cases equal

private def codec : Encode.TotalCodec (List Value) Value := Encode.list
private def input : List Value := [.blob payload]

example : ∃ tree : Named Bool, tree.erase = codec.encode input ∧ tree.AdmittedBy policy ∧
    tree.Compatible available ∧ codec.decode? tree.erase = some input :=
  codec.lift_named_of_coverage input (by
    change ∀ index : Fin 1, (input.get index).NamingCoverage (available.selectedBy policy)
    intro index
    have only : index = 0 := Subsingleton.elim _ _
    subst index
    exact ⟨false, rfl, rfl⟩) available_binding

private def unchecked : Store Bool := ⟨graph objects, graph fun _ => none⟩
private def noChoice : Store Bool := ⟨nameGraph fun _ => none, nameGraph fun _ => none⟩

example : CanName policy nested (.ref (.obj true)) := .obj (.blob rfl) rfl

example : ¬ ∃ view, CanName (available.selectedBy noChoice) (Value.blob payload) view := by
  rintro ⟨_, choices⟩
  cases choices with
  | blob hit => cases hit.1

example : ¬ ∃ view, CanName (unchecked.selectedBy policy) nested view := by
  rintro ⟨_, choices⟩
  cases choices with
  | obj child _ =>
    cases child with
    | blob hit => cases hit.2

end Silmaril.Formats.Dasl
