module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Plain.Thms
import Silmaril.Wasm.Verify.Kernel.Defs

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Plain.Examples

open Silmaril.Formats Silmaril.Wasm.Component.Value

def compound : TypeOf :=
  .record [("values", .list (.option (.prim .u32))),
    ("events", .stream (some (.record [("owner", .own ⟨0⟩)])))]

theorem compound_admitted : Stored.checkSchema compound = .ok () := by kernel_rfl

def signature : PlainSignature :=
  ⟨⟨Unit, fun _ => compound, fun _ => .star⟩, fun _ => compound_admitted⟩

def payload : Stored.Payload compound :=
  ⟨.record [.list [.variant 0 none, .variant 1 (some (Val.u32 9))], .stream ⟨3⟩], by decide⟩

def tree : Stored.Tree signature.val :=
  AST.node () payload [AST.node () payload []]

theorem retains_typed_value_without_receipts :
    (Payload.equivPlain compound_admitted payload).val = ⟨payload.val, []⟩ :=
  Payload.equivPlain_observed compound_admitted payload

theorem tree_roundtrip : (Tree.equivPlain signature tree).erase = tree :=
  Tree.equivPlain_symm signature ▸ (Tree.equivPlain signature).left_inv tree

theorem inactive_own_rejected :
    Stored.checkSchema (.record [("items", .list (.option (.own ⟨0⟩)))]) =
      .error .ownedResourceNeedsIdentity := rfl

theorem nested_channel_borrow_rejected :
    Stored.checkSchema (.option (.future (some (.record [("scope", .borrow ⟨0⟩)])))) =
      .error .storedBorrow := rfl

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Plain.Examples
