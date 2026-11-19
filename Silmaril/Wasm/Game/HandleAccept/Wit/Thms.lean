module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Defs
import Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.Basic

/-!
# AST payload types as WIT value types: laws

* `toWit_simple`: the WIT type of a payload type is simple (`ValType.simple`: no `future` or
  `stream`), so `toSimple` lands in `SimpleType`;
* `toWit_injective`: different payload types have different WIT types;
* `valEquiv`, `valsEquiv` (in `Defs`) are equivalences; `valEquiv_injective` restates that the
  embedding of payload values into WIT values is injective.
-/

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit

open Silmaril.Formats Silmaril.Wasm.Component Silmaril.Wasm.Component.WIT

universe u v

variable {Ref : Type u} {Resource : Type v}

theorem toWit_simple (t : PTy) : (toWit t : WIT.ValType Ref Resource).simple = true :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.toWit_simple t

/-- A payload type as a simple WIT type. -/
def toSimple (t : PTy) : WIT.SimpleType Ref Resource := ⟨toWit t, toWit_simple t⟩

theorem toWit_injective :
    Function.Injective (toWit : PTy → WIT.ValType Ref Resource) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.toWit_injective

theorem valEquiv_injective (E : WIT.Env Ref Resource) (t : PTy) :
    Function.Injective (valEquiv E t) :=
  (valEquiv E t).injective

end Silmaril.Wasm.Game.HandleAccept.Wit
