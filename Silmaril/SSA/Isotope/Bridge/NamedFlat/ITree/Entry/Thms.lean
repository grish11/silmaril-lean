module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Defs
import Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Projection

/-! # Exact entry packet and store projection -/

public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry

open LambdaSSA (Region)
open LambdaSSA.Semantics.Interaction.Typed (AtomValues)
open Silmaril.Isotope.Semantics (encodeValue)

universe u
variable {κ : Type (u + 1)} [AtomValues κ]
  {Name : Type (u + 1)} [DecidableEq Name] {n : Nat}

local notation "V" => AtomValues.carrier (κ := κ)
local notation "Interp" => Ty.denote V

/-- The encoded runtime input to the dispatcher is exactly the record of the
erased fields supplied to the original named runner. -/
theorem inputEnv_packet (β : BoundCtx (Ty κ) n) (x : Interp (Region.packedInputType β.toList)) :
    Capture.packEnv n (inputEnv β x) = encodeValue V (Region.packedInputType β.toList) x :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.inputEnv_packet β x

/-- Distinct names allow every independent typed slot to be observed at its
own key in the total named store. -/
theorem store_at (names : Fin n → Name) (distinct : Function.Injective names)
    (β : BoundCtx (Ty κ) n) (x : Interp (Region.packedInputType β.toList)) (i : Fin n) :
    store names β x (names i) = inputEnv β x i.val := by
  simp only [store, Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.first_capture names distinct i,
    Option.map_some, Option.getD_some]

/-- A version-zero lookup uses the same record field as the mutable store. -/
theorem store_version_zero (names : Fin n → Name) (β : BoundCtx (Ty κ) n)
    (x : Interp (Region.packedInputType β.toList)) (name : Name) :
    store (fun i => (names i, (0 : Nat))) β x (name, 0) = store names β x name := by
  simp only [store, Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.first_version]

end Silmaril.Isotope.Bridge.NamedFlat.Entry
