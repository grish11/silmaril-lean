module

public import Silmaril.Formats.Dasl.Resolve.Defs

@[expose] public section

namespace Silmaril.Formats.Dasl

variable {Name : Type}

/-- A nontrivial observation resolves at least one edge below the root. -/
def Partial.HasKnownBinding (observed : Partial Name) : Prop :=
  (∃ name value, observed.bindings.objects name value) ∨ (∃ name bytes, observed.bindings.blobs name bytes)

/-- At least one immediate CAS edge has a decoded object or blob binding.
An immediate edge may be surrounded by arbitrarily many inline containers. -/
def Shallow.HasReadableLink (source : Shallow Name) (store : Store Name) : Prop :=
  (∃ name value, Link.obj name ∈ source.directLinks ∧ store.objects name value) ∨
    (∃ name bytes, Link.blob name ∈ source.directLinks ∧ store.blobs name bytes)

end Silmaril.Formats.Dasl
