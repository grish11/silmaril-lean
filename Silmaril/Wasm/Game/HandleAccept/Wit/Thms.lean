module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Defs
import Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.Basic

/-!
# AST payload types as WIT value types: laws

* `toWit_simple`: the WIT type of a payload type is simple (`ValType.simple`: no `future` or
  `stream`), so `toSimple` lands in `SimpleType`;
* `ofWit_toWit`: `ofWit` recovers a payload type from its WIT type, so
  `toWit_injective`: different payload types have different WIT types (in particular `bytes`
  is `list u8`, not a separate type); `toWitList_eq_map`;
* `interp_own`, `interp_borrow_isEmpty`: in the stored-tree environment `storedEnv` an `own`
  payload is a resource representation (`Nat`) and a `borrow` has no value;
* `valEquiv`, `valsEquiv` (in `Defs`) are equivalences; `valEquiv_injective` restates that the
  embedding of payload values into WIT values is injective.
-/

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit

open Silmaril.Formats Silmaril.Wasm.Component Silmaril.Wasm.Component.WIT

universe u

variable {Ref : Type u}

theorem toWit_simple (t : PTy) : (toWit t : WIT.ValType Ref Nat).simple = true :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.toWit_simple t

/-- A payload type as a simple WIT type. -/
def toSimple (t : PTy) : WIT.SimpleType Ref Nat := ⟨toWit t, toWit_simple t⟩

/-- **`ofWit` is a left inverse of `toWit`**: a payload type is recovered from its WIT type. -/
theorem ofWit_toWit (t : PTy) : ofWit (toWit t : WIT.ValType Ref Nat) = some t :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.ofWit_toWit t

theorem toWit_injective :
    Function.Injective (toWit : PTy → WIT.ValType Ref Nat) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.toWit_injective

theorem toWitList_eq_map (ps : List PTy) :
    (toWitList ps : List (WIT.ValType Ref Nat)) = ps.map toWit :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.toWitList_eq_map ps

theorem valEquiv_injective (named : Ref → Type) (t : PTy) :
    Function.Injective (valEquiv named t) :=
  (valEquiv named t).injective

/-- **An `own` payload is a resource representation** in the stored-tree environment. -/
theorem interp_own (named : Ref → Type) (r : Nat) :
    (toWit (.own r) : WIT.ValType Ref Nat).Interp (storedEnv named) = Nat := rfl

/-- **A stored tree holds no borrow**: `borrow<r>` has no value in the stored-tree environment. -/
theorem interp_borrow_isEmpty (named : Ref → Type) (r : Nat) :
    IsEmpty ((toWit (.borrow r) : WIT.ValType Ref Nat).Interp (storedEnv named)) :=
  inferInstanceAs (IsEmpty Empty)

end Silmaril.Wasm.Game.HandleAccept.Wit
