module

public import Silmaril.Wasm.Component.Reference.LegalBoundary.Defs

/-!
# The reference boundary map against the IR's coercions (proofs)

* `statusPayload_flatStatus`: the IR payload of the flat status of a boundary result is
  `crPayload` of it (`flatStatus` is `stuck` exactly where `crPayload` finds non-flat values);
* `payloadAnswer_toResult_flat`: an IR import answer of flat values of the right types is the
  Core result that the reference engine plugs into the importer for those values.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference.LegalBoundary

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Reference
  Silmaril.Wasm.Component.Reference.LegalBoundary Silmaril.Wasm.Game

theorem statusPayload_flatStatus {H : Type} (cr : Silmaril.Wasm.SingleThreaded.CallResult) :
    statusPayload (flatStatus (H := H) (.returned cr)) = crPayload cr := by
  cases cr with
  | values vs =>
    cases h : vs.mapM Silmaril.Wasm.SingleThreaded.toFlat? <;>
      simp [flatStatus, h, statusPayload, crPayload]
  | trap => rfl

theorem payloadAnswer_toResult_flat {ft : FnType} {ys : List Flat} {vs : Typed ft.results}
    (h : typed? ft.results (ys.map Silmaril.Wasm.SingleThreaded.ofFlat) = some vs) :
    (payloadAnswer ft (some (.flat ys))).toResult.toAdmin = (Core3.toCR (.values ys)).toAdmin := by
  have hv : vs.1 = ys.map Silmaril.Wasm.SingleThreaded.ofFlat := by
    unfold typed? at h
    split at h
    · cases h; rfl
    · cases h
  simp only [payloadAnswer, h, Answer.toResult, Core3.toCR, hv]
  rfl

end Silmaril.Proofs.Wasm.Component.Reference.LegalBoundary
