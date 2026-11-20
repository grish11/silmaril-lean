module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Fragments.Defs
public import Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Canon.Defs

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit

open Silmaril.Formats

/-- The existing memory decoder restricted to scalar payload types. -/
abbrev ScalarType.load (scalar : ScalarType) (memory : ByteArray) (address : Nat) :
    Option scalar.pty.Val := MemSound.WitAst.loadVal memory scalar.pty address

/-- The existing memory decoder restricted to compound payload types. This does not
lift resources or implement any ABI mode outside the existing decoder. -/
abbrev CompoundType.load (compound : CompoundType) (memory : ByteArray) (address : Nat) :
    Option compound.pty.Val := MemSound.WitAst.loadVal memory compound.pty address

end Silmaril.Wasm.Game.HandleAccept.Wit
