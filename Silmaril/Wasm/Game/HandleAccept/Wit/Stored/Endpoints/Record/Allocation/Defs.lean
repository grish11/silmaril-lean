module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Record.Defs

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.RecordLower.Field

/-- A path through active compiled values. Collection entries include the
entry record of a map, so its key and value both participate in descent.
Inactive sum arms have layouts but no compiled payload to visit. -/
inductive Descendant : Field → Field → Prop where
  | self (field : Field) : Descendant field field
  | aggregate {type fields child leaf} : child ∈ fields → Descendant child leaf →
      Descendant (.aggregate type fields) leaf
  | fixed {element length entries child leaf} : child ∈ entries → Descendant child leaf →
      Descendant (.fixed element length entries) leaf
  | dynamic {type element entries child leaf} : child ∈ entries → Descendant child leaf →
      Descendant (.dynamic type element entries) leaf
  | sum {type arms tag child leaf} : Descendant child leaf → Descendant (.sum type arms tag (some child)) leaf

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.RecordLower.Field
