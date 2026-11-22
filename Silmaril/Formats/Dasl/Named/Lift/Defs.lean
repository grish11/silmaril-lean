module

public import Silmaril.Formats.Dasl.Named.Defs

@[expose] public section

namespace Silmaril.Formats.Dasl

open Silmaril.Semantics.Naming

variable {Name : Type}

/-- Filter available bindings by a naming policy. For a partial selector, use
`nameGraph` in the relevant lane. A policy need not be binding or choose a
name for every target. -/
def Store.selectedBy (store choices : Store Name) : Store Name :=
  ⟨inter choices.objects store.objects, inter choices.blobs store.blobs⟩

/-- Sufficient coverage for bottom-up naming of this value. Visit every child of
each inline container and linked object. An object needs a name for each viable
shallow child result, a blob for its exact bytes. Inline leaves need no names.
This may be stronger than one successful `CanName` witness. -/
def Value.NamingCoverage (allowed : Store Name) : Value → Prop
  | .ref impossible => impossible.elim
  | Tree.obj _ child => NamingCoverage allowed child ∧
      ∀ ⦃shallow⦄, CanName allowed child shallow → ∃ name, allowed.objects name shallow
  | Tree.blob _ bytes => ∃ name, allowed.blobs name bytes
  | .dict _ children => ∀ key, NamingCoverage allowed (children key)
  | .list _ children => ∀ index, NamingCoverage allowed (children index)
  | _ => True

end Silmaril.Formats.Dasl
