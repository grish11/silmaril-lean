module

public import Silmaril.Formats.LeanNDJSON.Validate.Thms
public import Silmaril.ProofFormats.LeanNDJSON.MLTT.Decode.Defs
import all Silmaril.ProofFormats.LeanNDJSON.MLTT.Decode.Defs

public section

namespace Silmaril.Proofs.ProofFormats.LeanNDJSON.MLTT

open Silmaril.Formats.LeanNDJSON
open Silmaril.ProofFormats.LeanNDJSON.MLTT

theorem importEvents_serialValid {events : List Event} {signatureSize nodeBudget : Nat}
    {out : Imported} (h : importEvents signatureSize events nodeBudget = .ok out) :
    SerialValid .initial events := by
  apply (serialValid?_iff _ _).mp
  cases hcheck : serialValid? .initial events
  · simp [importEvents, hcheck, throw, bind, Except.bind] at h
  · rfl

end Silmaril.Proofs.ProofFormats.LeanNDJSON.MLTT
