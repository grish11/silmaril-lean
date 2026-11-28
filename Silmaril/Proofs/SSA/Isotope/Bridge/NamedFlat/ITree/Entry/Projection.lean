module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Defs

public section

namespace Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Entry

open Silmaril.Isotope Silmaril.Isotope.Bridge.NamedFlat
open Silmaril.Isotope.Bridge.NamedFlat.Entry
open LambdaSSA (Region)
open LambdaSSA.Semantics (Env extend extend_succ extend_zero)
open LambdaSSA.Semantics.Interaction.Typed (AtomValues)
open Silmaril.Isotope.Semantics (encodeValue)

universe u
variable {κ : Type (u + 1)} [AtomValues κ]

local notation "V" => AtomValues.carrier (κ := κ)
local notation "Interp" => Ty.denote V

theorem inputEnv_packet {n : Nat} (β : BoundCtx (Ty κ) n)
    (x : Interp (Region.packedInputType β.toList)) :
    Capture.packEnv n (inputEnv β x) = encodeValue V (Region.packedInputType β.toList) x := by
  induction β with
  | nil => rfl
  | snoc β A ih =>
    change Value.pair (Capture.packEnv _ (extend (inputEnv β x.1) (encodeValue V A x.2) ∘ Nat.succ))
      (encodeValue V A x.2) =
      Value.pair (encodeValue V (Region.packedInputType β.toList) x.1) (encodeValue V A x.2)
    rw [show extend (inputEnv β x.1) (encodeValue V A x.2) ∘ Nat.succ = inputEnv β x.1 from rfl,
      ih]

theorem first_capture {Name : Type (u + 1)} [DecidableEq Name] {n : Nat}
    (names : Fin n → Name) (distinct : Function.Injective names) (i : Fin n) :
    first names (names i) = some i := by
  unfold first
  cases h : (List.finRange n).find? (fun j => decide (names j = names i)) with
  | some j =>
    have hit := List.find?_some (p := fun j => decide (names j = names i)) h
    exact congrArg some (distinct (of_decide_eq_true hit))
  | none =>
    have no := List.find?_eq_none.mp h i (by simp)
    simp at no

theorem first_version {Name : Type (u + 1)} [DecidableEq Name] {n : Nat}
    (names : Fin n → Name) (x : Name) :
    first (fun i => (names i, (0 : Nat))) (x, 0) = first names x := by
  unfold first
  congr 1
  funext i
  simp

end Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Entry
