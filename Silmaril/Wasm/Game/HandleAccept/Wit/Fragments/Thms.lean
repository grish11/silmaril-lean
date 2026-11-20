module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Fragments.Defs
public import Silmaril.Wasm.Game.HandleAccept.Wit.Thms

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit

open Silmaril.Formats Silmaril.Wasm.Component

universe u

variable {Ref : Type u}

theorem ScalarType.toWit_pty (scalar : ScalarType) :
    (Wit.toWit scalar.pty : WIT.ValType Ref Nat) = scalar.toWit := by
  rcases scalar with ⟨prim, _⟩
  cases prim <;> rfl

theorem ScalarType.ofWit_toWit (scalar : ScalarType) :
    ScalarType.ofWit (scalar.toWit : WIT.ValType Ref Nat) = some scalar := by
  rcases scalar with ⟨prim, scalar⟩
  simp [ScalarType.toWit, ScalarType.ofWit, ScalarType.ofPrimitive, scalar]

theorem ScalarType.ofPayload_pty (scalar : ScalarType) :
    ScalarType.ofPayload scalar.pty = some scalar := by
  simp only [ScalarType.ofPayload, ScalarType.toWit_pty, ScalarType.ofWit_toWit]

theorem ScalarType.toWit_injective :
    Function.Injective (ScalarType.toWit : ScalarType → WIT.ValType Ref Nat) := by
  intro first second equal
  simpa only [ScalarType.ofWit_toWit, Option.some.injEq] using congrArg ScalarType.ofWit equal

theorem ScalarType.pty_injective : Function.Injective ScalarType.pty := by
  intro first second equal
  simpa only [ScalarType.ofPayload_pty, Option.some.injEq] using congrArg ScalarType.ofPayload equal

theorem ScalarType.wellFormed {Resource : Type} (scalar : ScalarType)
    (refOk : Ref → Prop) (resourceOk : Resource → Prop) :
    (WIT.ValType.prim scalar.val).WellFormed refOk resourceOk := .prim _

def ScalarType.valEquiv (named : Ref → Type) (scalar : ScalarType) :
    scalar.pty.Val ≃ scalar.toWit.Interp (storedEnv named) :=
  scalar.toWit_pty (Ref := Ref) ▸ Wit.valEquiv named scalar.pty

theorem CompoundType.ofPayload_pty (compound : CompoundType) :
    CompoundType.ofPayload compound.pty = some compound := by
  rcases compound with ⟨type, compound⟩
  simp [CompoundType.pty, CompoundType.ofPayload, compound]

theorem CompoundType.ofWit_toWit (compound : CompoundType) :
    CompoundType.ofWit (compound.toWit : WIT.ValType Ref Nat) = some compound := by
  simp [CompoundType.ofWit, CompoundType.toWit, Wit.ofWit_toWit, CompoundType.ofPayload_pty]

theorem CompoundType.pty_injective : Function.Injective CompoundType.pty :=
  fun _ _ equal => Subtype.ext equal

theorem CompoundType.toWit_injective :
    Function.Injective (CompoundType.toWit : CompoundType → WIT.ValType Ref Nat) :=
  fun _ _ equal => CompoundType.pty_injective (Wit.toWit_injective equal)

def CompoundType.valEquiv (named : Ref → Type) (compound : CompoundType) :
    compound.pty.Val ≃ compound.toWit.Interp (storedEnv named) :=
  Wit.valEquiv named compound.pty

end Silmaril.Wasm.Game.HandleAccept.Wit
