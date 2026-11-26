module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Record.Defs

public section

namespace Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Record

open Silmaril.Isotope
open Silmaril.Isotope.Bridge.NamedFlat.Entry (inputEnv)
open Silmaril.Isotope.Bridge.NamedFlat.Entry.Record
open LambdaSSA.Semantics (extend_zero extend_succ)
open LambdaSSA.Semantics.Interaction.Typed (AtomValues)
open Silmaril.Isotope.Semantics (encodeValue)

universe u
variable {κ : Type (u + 1)} [AtomValues κ] {n m : Nat}

local notation "C" => AtomValues.carrier (κ := κ)

private theorem inputEnv_field (β : BoundCtx (Ty κ) n) (record : Input β) (i : Fin n) :
    inputEnv β record i.val = encodeValue C (β.get i) (field β record i) := by
  induction β with
  | nil => exact i.elim0
  | snoc β A ih =>
    exact Fin.cases rfl (fun j => (extend_succ ..).trans (ih record.1 j)) i

private theorem field_ofFields (β : BoundCtx (Ty κ) n)
    (fields : (i : Fin n) → Ty.denote C (β.get i)) (i : Fin n) :
    field β (ofFields β fields) i = fields i := by
  induction β with
  | nil => exact i.elim0
  | snoc β A ih => exact Fin.cases rfl (fun j => ih (fun i => fields i.succ) j) i

private theorem encode_cast {A B : Ty κ} (eq : A = B) (value : Ty.denote C A) :
    encodeValue C B ((congrArg (Ty.denote C) eq) ▸ value) = encodeValue C A value := by
  cases eq
  rfl

theorem inputEnv_reindex {β : BoundCtx (Ty κ) n} {γ : BoundCtx (Ty κ) m}
    (slots : BoundCtx.Renaming β γ) (record : Input γ) (i : Fin n) :
    inputEnv β (reindex slots record) i.val = inputEnv γ record (slots.toFun i).val := by
  rw [inputEnv_field β, inputEnv_field γ, reindex, field_ofFields]
  exact encode_cast (slots.typed i) _

end Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Record
