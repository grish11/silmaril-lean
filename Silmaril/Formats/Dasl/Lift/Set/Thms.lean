module

public import Silmaril.Formats.Dasl.Lift.Set.Defs

public section

namespace Silmaril.Formats.Dasl.Lift

open Silmaril.Semantics.Naming (Binding Relation)

variable {Key Item : Type} [LinearOrder Key]

theorem codedSet_binding {Surface : Type} {layout : Relation Surface (Finset Key)} (bound : Binding layout)
    (label : Encode.TotalCodec Item Key) : Binding (codedSet layout label) :=
  fun _ _ _ left right => Finset.image_injective label.injective (bound left right)

theorem orderedSet_binding (key : Encode.TotalCodec Key Value) : Binding (orderedSet key) :=
  fun _ _ _ ⟨_, first, left⟩ ⟨_, second, right⟩ =>
    left.symm.trans ((Encode.setOf key).injective (first.trans second.symm) ▸ right)

theorem orderedSet_encode (key : Encode.TotalCodec Key Value) (keys : Finset Key) :
    orderedSet key ((Encode.setOf key).encode (orderedKeySet keys)) keys :=
  ⟨_, rfl, by simp [orderedKeySet, Semantics.OrderedMap.keys, Function.comp_def, Finset.sort_toFinset]⟩

end Silmaril.Formats.Dasl.Lift
