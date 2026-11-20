module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Own.Nested.Defs
import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitOwnNested

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Own.Nested

open Silmaril.Formats

/-- Decoding the raw shape uses the same memory32 layout, including nested offsets. -/
theorem rawType_layout (type : PTy) : PTy.layout (rawType type) = PTy.layout type :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitOwnNested.rawType_layout type

theorem rawTypes_layout (types : List PTy) : PTy.layouts (rawTypes types) = PTy.layouts types :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitOwnNested.rawTypes_layout types

/-- Committing reservations makes each selected slot unavailable to all future lookups,
until another operation allocates the slot. This is a slot claim, not a claim of unique `rep`. -/
theorem commit_dead (rt : RT) (reserved : Reservations) {index : BitVec 32}
    (member : index ∈ reserved.val) : (rt.killAll reserved.val).Dead index := by
  intro resource
  simp only [RT.lookup, RT.killAll, ite_eq_left member]
  cases rt index <;> rfl

end Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Own.Nested
