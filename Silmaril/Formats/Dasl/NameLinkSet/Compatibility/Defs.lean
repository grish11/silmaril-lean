module

public import Silmaril.Formats.Dasl.LinkedSet.Thms
public import Silmaril.Formats.Dasl.NameLinkSet.Thms

@[expose] public section

namespace Silmaril.Formats.Dasl.NameLinkSet

open Silmaril.Semantics

variable {Name Object : Type}

/-- Reindex existing typed links, without resolving them or choosing new names.
This is a layout conversion, not a reinterpretation of the old wire format. -/
def ofContentLayout [LinearOrder Name] (layout : LinkedSet.Layout Name) : Layout (MixedKey Name) :=
  normalize (layout.entries.map (taggedKey ∘ Prod.snd))

/-- The graph of the content-ordered layout's reader; a failed read provides no binding. -/
def readerRelation (reader : LinkedSet.Reader Object Name) : Naming.Relation (Link Name) (LinkedSet.Item Object) :=
  fun link value => reader.resolve? link = some value

end Silmaril.Formats.Dasl.NameLinkSet
