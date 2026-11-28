module

public import Silmaril.Logic.Temporal.TLA.Data.Tagged.Collections.Defs
import Mathlib.Logic.Small.Basic

/-! Exact tuple decoding and flat Cartesian products for collection binders. -/

@[expose] public section

namespace Silmaril.Logic.Temporal.TLA.Data.Tagged

universe u

/-- Recognize the mathematical tuple graph at exactly the requested length. -/
noncomputable def Value.untuple (arity : Nat) (value : Value.{u}) : Option (List Value.{u}) :=
  (decode (fun xs : {xs : List Value.{u} // xs.length = arity} => Value.tuple xs.val) value).map
    Subtype.val

/-- Each index selects a member from its own small set. Replacement forms the
set of tuple graphs from all selections, including when a factor is infinite. -/
noncomputable def SetData.cartesian (bounds : List SetData.{u}) : SetData.{u} :=
  ⟨ZFSet.range fun select : (i : Fin bounds.length) → (bounds[i.val]).codes =>
    (Value.tuple (List.ofFn fun i => ⟨(select i).val⟩)).code⟩

/-- Decode the operands as sets before forming the flat product. -/
noncomputable def Value.cartesian (bounds : List Value.{u}) : Option Value.{u} :=
  (bounds.mapM Value.asSet).map (Value.set ∘ SetData.cartesian)

end Silmaril.Logic.Temporal.TLA.Data.Tagged
