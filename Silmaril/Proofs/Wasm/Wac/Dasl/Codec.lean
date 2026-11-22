module

public import Silmaril.Wasm.Wac.Dasl.Defs

public section

namespace Silmaril.Proofs.Wasm.Wac.Dasl.Codec

open Silmaril.Formats.Dasl
open Silmaril.Wasm.Wac Dasl
open Silmaril.Wasm.Component (ValTy)

variable {Name Ref : Type}

theorem inline_roundtrip (tree : Inline) : readInline (embedInline (Ref := Ref) (Name := Name) tree) = some tree := by
  induction tree with
  | ref impossible | obj impossible _ _ | blob impossible _ => exact impossible.elim
  | dict _ _ ih | list _ _ ih =>
    simp only [embedInline] at ih
    simp [readInline, embedInline, Tree.map, ih]
  | _ => rfl

theorem src_roundtrip (source : Src) : srcRead (srcWrite source) = some source := by
  cases source <;> simp [srcRead, srcWrite, Encode.list, natural, Nat.toNat?_repr]

private theorem list_read_map {Source Target : Type} (read : Source → Option Target) (values : List Source) :
    (List.ofFn fun index => read (values.get index)).mapM id = values.mapM read := by
  change (List.ofFn (read ∘ values.get)).mapM id = _
  rw [← List.map_ofFn, List.ofFn_get, List.mapM_map]
  rfl

private theorem type_not_null (ty : ValTy) : typeWrite ty ≠ .null := by
  cases ty <;> simp [typeWrite, Encode.list]

mutual
theorem type_roundtrip (ty : ValTy) : typeRead (typeWrite ty) = some ty := by
  cases ty with
  | record fields =>
    change ((List.ofFn fun index => typeRead ((typesWrite fields).get index)).mapM id).map ValTy.record = _
    rw [list_read_map, types_roundtrip]
    rfl
  | variant cases =>
    change ((List.ofFn fun index => caseRead ((casesWrite cases).get index)).mapM id).map ValTy.variant = _
    rw [list_read_map, cases_roundtrip]
    rfl
  | _ => rfl
termination_by structural ty

theorem types_roundtrip (types : List ValTy) : (typesWrite types).mapM typeRead = some types := by
  cases types with
  | nil => rfl
  | cons ty rest => simp [typesWrite, type_roundtrip ty, types_roundtrip rest]
termination_by structural types

theorem cases_roundtrip (cases : List (Option ValTy)) : (casesWrite cases).mapM caseRead = some cases := by
  cases cases with
  | nil => rfl
  | cons head rest =>
    cases head with
    | none => simp [casesWrite, caseRead, cases_roundtrip rest]
    | some ty =>
      have hit : caseRead (typeWrite ty) = some (some ty) := by
        generalize eq : typeWrite ty = tree
        cases tree <;> first
          | exact False.elim (type_not_null ty eq)
          | simp [caseRead, ← eq, type_roundtrip ty]
      simp [casesWrite, hit, cases_roundtrip rest]
termination_by structural cases
end

end Silmaril.Proofs.Wasm.Wac.Dasl.Codec
