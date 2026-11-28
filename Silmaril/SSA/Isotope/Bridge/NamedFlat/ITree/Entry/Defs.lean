module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Capture.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Semantics.ITree.Ordered.Flat.Entry.Institution.Thms

/-! # Project a supplied typed record to a named input store -/

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry

open LambdaSSA (Region)
open LambdaSSA.Semantics (Env extend)
open LambdaSSA.Semantics.Interaction.Typed (AtomValues)
open Silmaril.Isotope.Semantics (encodeValue)

universe u
variable {κ : Type (u + 1)} [AtomValues κ]

local notation "V" => AtomValues.carrier (κ := κ)
local notation "Interp" => Ty.denote V

/-- Decode each typed field to its tagged runtime value. Slots outside the
context are unit. The newest slot is the right field of the input product. -/
def inputEnv : {n : Nat} → (β : BoundCtx (Ty κ) n) →
    Interp (Region.packedInputType β.toList) → Env (Sigma V)
  | _, .nil, _ => fun _ => .unit
  | _, .snoc β A, x => extend (inputEnv β x.1) (encodeValue V A x.2)

/-- Use the elaborator's exact lookup order on the shared supplied fields. -/
def store {Name : Type (u + 1)} [DecidableEq Name] {n : Nat} (names : Fin n → Name)
    (β : BoundCtx (Ty κ) n) (x : Interp (Region.packedInputType β.toList)) :
    Name → Value (Sigma V) :=
  fun name => ((first names name).map (fun i => inputEnv β x i.val)).getD .unit

end Silmaril.Isotope.Bridge.NamedFlat.Entry
