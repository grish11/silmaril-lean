module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Defs

/-!
# Proofs: AST payload types as WIT value types

* `toWit_simple`: the WIT type of a payload type is simple (no `future` or `stream`);
* `toWit_injective`: different payload types have different WIT types.

New proofs (no source).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Wit

open Silmaril.Formats Silmaril.Wasm.Component Silmaril.Wasm.Component.WIT
  Silmaril.Wasm.Game.HandleAccept.Wit

universe u v

variable {Ref : Type u} {Resource : Type v}

theorem toWit_simple : ∀ t : PTy, (toWit t : WIT.ValType Ref Resource).simple = true
  | .bool | .s32 | .u32 | .s64 | .u64 | .string => by
      simp [toWit, WIT.ValType.simple]
  | .bytes => by simp [toWit, WIT.ValType.simple]
  | .list t => by simpa [toWit, WIT.ValType.simple] using toWit_simple t

theorem toWit_injective :
    Function.Injective (toWit : PTy → WIT.ValType Ref Resource) := by
  intro a b h
  induction a generalizing b with
  | list a ih =>
      cases b with
      | list b =>
          simp only [toWit, WIT.ValType.list.injEq] at h
          exact congrArg _ (ih h)
      | bytes =>
          simp only [toWit, WIT.ValType.list.injEq] at h
          cases a <;> simp [toWit] at h
      | _ => simp [toWit] at h
  | bytes =>
      cases b with
      | list b =>
          simp only [toWit, WIT.ValType.list.injEq] at h
          cases b <;> simp [toWit] at h
      | bytes => rfl
      | _ => simp [toWit] at h
  | _ => cases b <;> first | rfl | simp [toWit] at h

end Silmaril.Proofs.Wasm.Game.HandleAccept.Wit
