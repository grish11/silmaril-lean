module

public import Silmaril.Formats.Dasl.StringObjectMap.Defs
import Silmaril.Proofs.Formats.Dasl.StringObjectMap

public section

namespace Silmaril.Formats.Dasl.StringObjectMap

open Silmaril.Semantics (OrderedMap)

variable {Name : Type} {read : Read Name} {store : Store Name}

theorem layout_eq_iff {left right : Layout Name} : left = right ↔ ∀ key, left.lookup? key = right.lookup? key :=
  ⟨fun same _ => same ▸ rfl, OrderedMap.eq_of_lookup⟩

theorem cardinality_eq (layout : Layout Name) : cardinality layout = (keySet layout).card := by
  rw [keySet, List.toFinset_card_of_nodup layout.keys_nodup]
  simp [cardinality, OrderedMap.keys]

theorem decode_lookup (layout : Layout Name) (key : String) :
    (codec.decode? (codec.encode layout)).map (fun recovered => recovered.lookup? key) = some (layout.lookup? key) := by
  rw [codec.recovers]
  rfl

theorem recover_sound (sound : Read.Sound read store)
    {entry : Option (Placement Name)} {value : Option (Shallow Name)}
    (hit : recover read entry = .ok value) : LookupSpec store entry value :=
  Proofs.Formats.Dasl.StringObjectMap.recover_sound sound hit

theorem recover_iff (sound : Read.Sound read store)
    (complete : ∀ ⦃name value⦄, store.objects name value → read name = .found value)
    {entry : Option (Placement Name)} {value : Option (Shallow Name)} :
    recover read entry = .ok value ↔ LookupSpec store entry value :=
  ⟨recover_sound sound, Proofs.Formats.Dasl.StringObjectMap.recover_complete complete⟩

theorem lookup_sound (sound : Read.Sound read store) {layout : Layout Name} {key : String}
    {value : Option (Shallow Name)} (hit : lookup layout read key = .ok value) :
    LookupSpec store (layout.lookup? key) value := recover_sound sound hit

end Silmaril.Formats.Dasl.StringObjectMap
