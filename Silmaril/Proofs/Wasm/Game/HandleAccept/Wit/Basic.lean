module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Defs

/-!
# Proofs: AST payload types as WIT value types

* `toWit_simple`: the WIT type of a payload type is simple (no `future` or `stream`);
* `ofWit_toWit` (with `ofWitList_toWitList`, `ofWitFields_toWitFields`,
  `ofWitCases_toWitCases`, `ofWitOpt_toWitOpt`): `ofWit` is a left inverse of `toWit`;
* `toWit_injective`: different payload types have different WIT types;
* `toWitList_eq_map`: `toWitList` is `List.map toWit`.

New proofs (no source).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Wit

open Silmaril.Formats Silmaril.Wasm.Component Silmaril.Wasm.Component.WIT
  Silmaril.Wasm.Game.HandleAccept.Wit

universe u

variable {Ref : Type u}

mutual
theorem toWit_simple : ∀ t : PTy, (toWit t : WIT.ValType Ref Nat).simple = true
  | .bool | .s32 | .u32 | .s64 | .u64 | .string | .s8 | .u8 | .s16 | .u16 | .f32 | .f64
  | .char | .enum _ | .flags _ | .own _ | .borrow _ => by
      simp [toWit, WIT.ValType.simple]
  | .list t => by simpa [toWit, WIT.ValType.simple] using toWit_simple t
  | .fixedList t _ => by simpa [toWit, WIT.ValType.simple] using toWit_simple t
  | .option t => by simpa [toWit, WIT.ValType.simple] using toWit_simple t
  | .record fs => by simpa [toWit, WIT.ValType.simple] using toWitFields_simple fs
  | .tuple ts => by simpa [toWit, WIT.ValType.simple] using toWitList_simple ts
  | .variant cs => by simpa [toWit, WIT.ValType.simple] using toWitCases_simple cs
  | .result ok err => by
      simp [toWit, WIT.ValType.simple, toWitOpt_simple ok, toWitOpt_simple err]

theorem toWitList_simple : ∀ ts : List PTy,
    WIT.ValType.simpleList (toWitList ts : List (WIT.ValType Ref Nat)) = true
  | [] => by simp [toWitList, WIT.ValType.simpleList]
  | t :: ts => by
      simp [toWitList, WIT.ValType.simpleList, toWit_simple t, toWitList_simple ts]

theorem toWitFields_simple : ∀ fs : List (String × PTy),
    WIT.ValType.simpleFields (toWitFields fs : List (String × WIT.ValType Ref Nat)) = true
  | [] => by simp [toWitFields, WIT.ValType.simpleFields]
  | (_, t) :: fs => by
      simp [toWitFields, WIT.ValType.simpleFields, toWit_simple t, toWitFields_simple fs]

theorem toWitCases_simple : ∀ cs : List (String × Option PTy),
    WIT.ValType.simpleCases
      (toWitCases cs : List (String × Option (WIT.ValType Ref Nat))) = true
  | [] => by simp [toWitCases, WIT.ValType.simpleCases]
  | (_, o) :: cs => by
      simp [toWitCases, WIT.ValType.simpleCases, toWitOpt_simple o, toWitCases_simple cs]

theorem toWitOpt_simple : ∀ o : Option PTy,
    WIT.ValType.simpleOpt (toWitOpt o : Option (WIT.ValType Ref Nat)) = true
  | none => by simp [toWitOpt, WIT.ValType.simpleOpt]
  | some t => by simpa [toWitOpt, WIT.ValType.simpleOpt] using toWit_simple t
end

mutual
theorem ofWit_toWit : ∀ t : PTy, ofWit (toWit t : WIT.ValType Ref Nat) = some t
  | .bool | .s32 | .u32 | .s64 | .u64 | .string | .s8 | .u8 | .s16 | .u16 | .f32 | .f64
  | .char | .enum _ | .flags _ | .own _ | .borrow _ => by
      simp [toWit, ofWit, ofPrim]
  | .list t => by simp [toWit, ofWit, ofWit_toWit t]
  | .fixedList t _ => by simp [toWit, ofWit, ofWit_toWit t]
  | .option t => by simp [toWit, ofWit, ofWit_toWit t]
  | .record fs => by simp [toWit, ofWit, ofWitFields_toWitFields fs]
  | .tuple ts => by simp [toWit, ofWit, ofWitList_toWitList ts]
  | .variant cs => by simp [toWit, ofWit, ofWitCases_toWitCases cs]
  | .result ok err => by
      simp [toWit, ofWit, ofWitOpt_toWitOpt ok, ofWitOpt_toWitOpt err]

theorem ofWitList_toWitList : ∀ ts : List PTy,
    ofWitList (toWitList ts : List (WIT.ValType Ref Nat)) = some ts
  | [] => by simp [toWitList, ofWitList]
  | t :: ts => by simp [toWitList, ofWitList, ofWit_toWit t, ofWitList_toWitList ts]

theorem ofWitFields_toWitFields : ∀ fs : List (String × PTy),
    ofWitFields (toWitFields fs : List (String × WIT.ValType Ref Nat)) = some fs
  | [] => by simp [toWitFields, ofWitFields]
  | (_, t) :: fs => by
      simp [toWitFields, ofWitFields, ofWit_toWit t, ofWitFields_toWitFields fs]

theorem ofWitCases_toWitCases : ∀ cs : List (String × Option PTy),
    ofWitCases (toWitCases cs : List (String × Option (WIT.ValType Ref Nat))) = some cs
  | [] => by simp [toWitCases, ofWitCases]
  | (_, o) :: cs => by
      simp [toWitCases, ofWitCases, ofWitOpt_toWitOpt o, ofWitCases_toWitCases cs]

theorem ofWitOpt_toWitOpt : ∀ o : Option PTy,
    ofWitOpt (toWitOpt o : Option (WIT.ValType Ref Nat)) = some o
  | none => by simp [toWitOpt, ofWitOpt]
  | some t => by simp [toWitOpt, ofWitOpt, ofWit_toWit t]
end

theorem toWit_injective :
    Function.Injective (toWit : PTy → WIT.ValType Ref Nat) := by
  intro a b h
  have h' := congrArg ofWit h
  rw [ofWit_toWit, ofWit_toWit] at h'
  exact Option.some.inj h'

theorem toWitList_eq_map : ∀ ps : List PTy,
    (toWitList ps : List (WIT.ValType Ref Nat)) = ps.map toWit
  | [] => rfl
  | t :: ps => by rw [toWitList, toWitList_eq_map ps, List.map_cons]

end Silmaril.Proofs.Wasm.Game.HandleAccept.Wit
