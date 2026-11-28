module

public import Silmaril.ProofFormats.LeanNDJSON.MLTT.Decode.Defs
import Silmaril.Proofs.ProofFormats.LeanNDJSON.MLTT.Decode

public section

namespace Silmaril.ProofFormats.LeanNDJSON.MLTT

open Silmaril.Formats.LeanNDJSON

/-- Every successfully imported stream satisfies the codec's serial reference contract. -/
theorem importEvents_serialValid {events : List Event} {signatureSize nodeBudget : Nat}
    {out : Imported} (h : importEvents signatureSize events nodeBudget = .ok out) :
    SerialValid .initial events :=
  Silmaril.Proofs.ProofFormats.LeanNDJSON.MLTT.importEvents_serialValid h

end Silmaril.ProofFormats.LeanNDJSON.MLTT
