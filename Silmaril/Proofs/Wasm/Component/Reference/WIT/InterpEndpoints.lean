module

public import Silmaril.Wasm.Component.Reference.WIT.Interp.Defs

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference.WIT.InterpEndpoints

open Silmaril.Wasm.Component.WIT

universe u v
variable {Ref : Type u} {Resource : Type v} (E : Env Ref Resource)
  (futureEnd streamEnd : Option (ValType Ref Resource) → Type)

local notation "Extended" => E.withEndpoints futureEnd streamEnd

mutual
theorem interp : (type : ValType Ref Resource) → type.simple = true →
    type.Interp Extended = type.Interp E
  | .prim _, _ | .ref _, _ | .enum _, _ | .flags _, _ | .own _, _ | .borrow _, _
  | .errorContext, _ => rfl
  | .list type, simple | .fixedList type _, simple | .option type, simple | .map _ type, simple => by
    simp only [ValType.Interp, interp type simple]
  | .record types, simple => fields types simple
  | .tuple types, simple => vector types simple
  | .variant types, simple => cases types simple
  | .result ok error, simple => by
    have both := Bool.and_eq_true_iff.mp simple
    simp only [ValType.Interp, optional ok both.1, optional error both.2]
  | .future _, simple | .stream _, simple => nomatch simple

theorem fields : (types : List (String × ValType Ref Resource)) → ValType.simpleFields types = true →
    ValType.InterpFields Extended types = ValType.InterpFields E types
  | [], _ => rfl
  | (_, type) :: types, simple => by
    have both := Bool.and_eq_true_iff.mp simple
    simp only [ValType.InterpFields, interp type both.1, fields types both.2]

theorem vector : (types : List (ValType Ref Resource)) → ValType.simpleList types = true →
    ValType.InterpList Extended types = ValType.InterpList E types
  | [], _ => rfl
  | type :: types, simple => by
    have both := Bool.and_eq_true_iff.mp simple
    simp only [ValType.InterpList, interp type both.1, vector types both.2]

theorem cases : (types : List (String × Option (ValType Ref Resource))) → ValType.simpleCases types = true →
    ValType.InterpCases Extended types = ValType.InterpCases E types
  | [], _ => rfl
  | (_, type) :: types, simple => by
    have both := Bool.and_eq_true_iff.mp simple
    simp only [ValType.InterpCases, optional type both.1, cases types both.2]

theorem optional : (type : Option (ValType Ref Resource)) → ValType.simpleOpt type = true →
    ValType.InterpOpt Extended type = ValType.InterpOpt E type
  | none, _ => rfl
  | some type, simple => interp type simple
end

end Silmaril.Proofs.Wasm.Component.Reference.WIT.InterpEndpoints
