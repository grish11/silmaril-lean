module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Fragments.Defs
public import Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Thms
public import Silmaril.Wasm.Game.HandleAccept.Wit.Fragments.Thms

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit

open Silmaril.Wasm.Component

universe u

variable {Ref : Type u}

theorem ScalarType.layout_toWit (scalar : ScalarType) :
    ABI.layout .i32 (scalar.toWit : WIT.ClosedType Nat) = MemSound.WitAst.PTy.layout scalar.pty := by
  rw [← scalar.toWit_pty]
  exact MemSound.WitAst.layout_toWit scalar.pty

/-- The compound's memory32 ABI representation layout, not a semantics for resource moves. -/
theorem CompoundType.layout_toWit (compound : CompoundType) :
    ABI.layout .i32 (compound.toWit : WIT.ClosedType Nat) = MemSound.WitAst.PTy.layout compound.pty :=
  MemSound.WitAst.layout_toWit compound.pty

/-- Transporting the decoder result to WIT and back preserves both values and failure. -/
theorem ScalarType.load_roundtrip (scalar : ScalarType) (named : Ref → Type)
    (memory : ByteArray) (address : Nat) :
    ((scalar.load memory address).map (scalar.valEquiv named)).map (scalar.valEquiv named).symm =
      scalar.load memory address := by
  cases scalar.load memory address <;> simp

/-- Transporting a compound result does not change the existing memory decoder's domain. -/
theorem CompoundType.load_roundtrip (compound : CompoundType) (named : Ref → Type)
    (memory : ByteArray) (address : Nat) :
    ((compound.load memory address).map (compound.valEquiv named)).map (compound.valEquiv named).symm =
      compound.load memory address := by
  cases compound.load memory address <;> simp

end Silmaril.Wasm.Game.HandleAccept.Wit
