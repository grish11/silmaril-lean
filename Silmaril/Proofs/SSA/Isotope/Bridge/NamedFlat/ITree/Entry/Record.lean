module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Record.Defs

public section

namespace Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Record

open Silmaril.Isotope
open Silmaril.Isotope.Bridge.NamedFlat.Entry (inputEnv)
open Silmaril.Isotope.Bridge.NamedFlat.Entry.Record
open LambdaSSA.Semantics (extend_zero extend_succ)
open LambdaSSA.Semantics.Interaction.Typed (AtomValues)
open Silmaril.Isotope.Semantics (encodeValue encodeValue_injective)

universe u
variable {κ : Type (u + 1)} [AtomValues κ] {n m : Nat}

local notation "C" => AtomValues.carrier (κ := κ)

theorem inputEnv_field (β : BoundCtx (Ty κ) n) (record : Input β) (i : Fin n) :
    inputEnv β record i.val = encodeValue C (β.get i) (field β record i) := by
  induction β with
  | nil => exact i.elim0
  | snoc β A ih =>
    exact Fin.cases rfl (fun j => (extend_succ ..).trans (ih record.1 j)) i

theorem field_ofFields (β : BoundCtx (Ty κ) n)
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

private theorem eq_of_inputEnv (β : BoundCtx (Ty κ) n) (left right : Input β)
    (agrees : ∀ i : Fin n, inputEnv β left i.val = inputEnv β right i.val) : left = right := by
  induction β with
  | nil =>
    change PUnit at left right
    exact Subsingleton.elim left right
  | snoc β A ih =>
    exact Prod.ext (ih left.1 right.1 (fun i => agrees i.succ))
      (encodeValue_injective C A (agrees 0))

theorem reindex_id (β : BoundCtx (Ty κ) n) (record : Input β) :
    reindex (.id β) record = record :=
  eq_of_inputEnv β _ _ (inputEnv_reindex (.id β) record)

theorem reindex_comp {β : BoundCtx (Ty κ) n} {γ : BoundCtx (Ty κ) m}
    {k : Nat} {δ : BoundCtx (Ty κ) k} (first : BoundCtx.Renaming β γ)
    (second : BoundCtx.Renaming γ δ) (record : Input δ) :
    reindex (first.comp second) record = reindex first (reindex second record) :=
  eq_of_inputEnv β _ _ fun i => (inputEnv_reindex (first.comp second) record i).trans
    (((inputEnv_reindex first (reindex second record) i).trans
      (inputEnv_reindex second record (first.toFun i))).symm)

end Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Record
