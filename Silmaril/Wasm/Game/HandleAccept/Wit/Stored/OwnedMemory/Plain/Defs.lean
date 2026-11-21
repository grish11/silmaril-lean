module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Conservative.Defs

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory

/-- Signatures admitted by the existing checked boundary. They have no direct owner
leaves, including inactive cases, and no stored borrows. A channel's element type
may contain owners: those are transferred separately from the endpoint. -/
def PlainSignature := { sig : Stored.Signature // ∀ tag, Stored.checkSchema (sig.payload tag) = .ok () }

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory
