module

public import Silmaril.Formats.Dasl.StringObjectMap.Defs

public section

namespace Silmaril.Proofs.Formats.Dasl.StringObjectMap

open Silmaril.Formats.Dasl Silmaril.Formats.Dasl.StringObjectMap

variable {Name : Type} {read : Read Name} {store : Store Name}

theorem recover_sound (sound : Read.Sound read store)
    {entry : Option (Placement Name)} {value : Option (Shallow Name)}
    (hit : recover read entry = .ok value) : LookupSpec store entry value := by
  rcases entry with _ | (inline | name)
  · cases hit
    trivial
  · cases hit
    rfl
  · cases found : read name <;> simp [recover, found] at hit
    subst value
    exact sound found

theorem recover_complete (complete : ∀ ⦃name value⦄, store.objects name value → read name = .found value)
    {entry : Option (Placement Name)} {value : Option (Shallow Name)}
    (spec : LookupSpec store entry value) : recover read entry = .ok value := by
  rcases entry with _ | (inline | name) <;> cases value <;> simp [LookupSpec] at spec
  · rfl
  · simp [recover, spec]
  · simp [recover, complete spec]

end Silmaril.Proofs.Formats.Dasl.StringObjectMap
