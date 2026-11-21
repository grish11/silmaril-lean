module

public import Silmaril.Wasi.Component.Accept.Ref.Typed.Defs
public import Silmaril.Wasi.Component.Accept.Defs
public import Silmaril.Wasm.Component.Reference.Bridge.Defs

/-! Proofs for `Silmaril.Wasi.Component.Accept.Ref.Bridge.Thms`. -/

@[expose] public section

namespace Silmaril.Proofs.Wasi.Component.Accept.Ref

open Silmaril.Wasi.Accept.Ref
open Silmaril.Wasm.Component.Reference (toRefVal toRefVals)

theorem toRefVals_eq_map :
    ∀ vs : List Silmaril.Wasm.Component.Val, toRefVals vs = vs.map toRefVal
  | [] => rfl
  | v :: vs => by simp [toRefVals, toRefVals_eq_map vs]

theorem u8Of?_toRefVal (v : Silmaril.Wasm.Component.Val) :
    u8Of? (toRefVal v) = Silmaril.Wasi.Accept.decodePrim .u8 v := by
  cases v with
  | u8 x =>
    have hx := x.isLt
    simp only [toRefVal, u8Of?, Silmaril.Wasi.Accept.decodePrim]
    have hc : (0 : Int) ≤ ↑x.toNat ∧ (↑x.toNat : Int) < 256 := ⟨by omega, by omega⟩
    simp only [hc, and_self, ↓reduceIte, Int.toNat_natCast, Option.some.injEq]
    apply UInt8.toBitVec_inj.mp
    simp
  | _ => simp [toRefVal, u8Of?, Silmaril.Wasi.Accept.decodePrim]

theorem bytesOf?_toRefVal (v : Silmaril.Wasm.Component.Val) :
    bytesOf? [toRefVal v] = Silmaril.Wasi.Accept.bytes? v := by
  cases v with
  | record vs =>
    simp only [toRefVal, bytesOf?, Silmaril.Wasi.Accept.bytes?, Silmaril.Wasi.Accept.ofRecord?,
      Option.bind_some, toRefVals_eq_map, List.mapM_map]
    congr 1
    funext x
    exact u8Of?_toRefVal x
  | _ => simp [toRefVal, bytesOf?, Silmaril.Wasi.Accept.bytes?, Silmaril.Wasi.Accept.ofRecord?]

end Silmaril.Proofs.Wasi.Component.Accept.Ref
