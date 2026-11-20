module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Defs

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory

/-- Forget owner receipts in a typed observation. This does not transfer authority. -/
def Payload.erase {type : Stored.TypeOf} (payload : Payload type) : Stored.Payload type :=
  ⟨payload.val.value, payload.property.1⟩

/-- Erase receipts throughout a tree, preserving tags, child order and arity. -/
def Tree.erase {sig : Stored.Signature} (tree : Tree sig) : Stored.Tree sig :=
  Silmaril.Formats.TExpr1.mapTag (fun field => ⟨field.1, Payload.erase field.2⟩) tree

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory
