module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Plain.Defs
import Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Plain

public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory

open Silmaril.Wasm.Component.Value

/-- Admitted old schemas need no owner receipts on any branch of a value. -/
theorem requirements_of_schema {type : Stored.TypeOf} (admitted : Stored.checkSchema type = .ok ())
    (value : Val) : ownerRequirements type value = [] :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Plain.requirements_of_schema admitted value

/-- The checked old payload injects into the receipt-aware family. On this domain
erasure is also a right inverse: no value can contain a spurious owner receipt. -/
def Payload.equivPlain {type : Stored.TypeOf} (admitted : Stored.checkSchema type = .ok ()) :
    Stored.Payload type ≃ Payload type :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Plain.payloadEquiv admitted

theorem Payload.equivPlain_symm {type : Stored.TypeOf} (admitted : Stored.checkSchema type = .ok ()) :
    ((Payload.equivPlain admitted).symm : Payload type → Stored.Payload type) = Payload.erase := by
  unfold Payload.equivPlain
  rfl

/-- Embed the existing checked AST using its original tags, child order and arity.
The equivalence is about observations and does not grant authority to move endpoints. -/
def Tree.equivPlain (signature : PlainSignature) : Stored.Tree signature.val ≃ Tree signature.val :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Plain.treeEquiv signature

theorem Payload.equivPlain_observed {type : Stored.TypeOf} (admitted : Stored.checkSchema type = .ok ())
    (payload : Stored.Payload type) : (Payload.equivPlain admitted payload).val =
      Observed.ordinary payload.val := by unfold Payload.equivPlain; rfl

/-- At the value boundary, checking an ordinary observation agrees with embedding
the old result, including the typed failure. This assumes no receipts were observed. -/
theorem checkValue_plain {type : Stored.TypeOf} (admitted : Stored.checkSchema type = .ok ())
    (value : Val) : checkValue type (Observed.ordinary value) =
      ((Stored.checkValue type value).map (Payload.equivPlain admitted)).mapError Issue.schema :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Plain.check_plain admitted value

theorem Tree.equivPlain_symm (signature : PlainSignature) :
    ((Tree.equivPlain signature).symm : Tree signature.val → Stored.Tree signature.val) = Tree.erase := by
  unfold Tree.equivPlain
  rfl

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory
