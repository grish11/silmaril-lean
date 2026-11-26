module

public import Silmaril.Formats.Arrow.MixedFlat.File.Events.Defs
public import Silmaril.Formats.Arrow.MixedFlat.File.Window.Projection.Thms
public import Mathlib.Data.List.Forall2
import Silmaril.Proofs.Formats.Arrow.MixedFlat.File.Events.Readback

public section

namespace Silmaril.Formats.Arrow.MixedFlat.File.Events

open Silmaril.Relational

/-- Successful eager decoding gives the exact checked footer schema, one
aligned event for each strict record observation in order, and EOS. -/
theorem read_exact {limits : MixedFlat.Limits} {input : KBytes}
    {source : Σ signature : Scan.Schema MixedFlat.Field Unit, Trace signature}
    (success : read limits input = .ok source) :
    ∃ index : MixedFlat.File.Index input,
      MixedFlat.File.readIndex limits.observation.ipc input = .ok index ∧
      source.1 = schema index.footer.fields ∧ source.2.termination = .eos ∧
      ∃ observed, index.footer.blocks.mapM (MixedFlat.File.readRecord limits input index.footer.fields) =
        .ok observed ∧ List.Forall₂ (Agrees source.1) observed source.2.batches :=
  Proofs.Formats.Arrow.MixedFlat.File.Events.read_exact success

/-- For a successfully drained file admitted in the full carrier window,
the actual keep-all event scan and indexed projection agree at each
ordinal, including absent indices and present zero-row batches. -/
theorem read_projectedAt_scan {limits : MixedFlat.Limits} {input : KBytes}
    {source : Σ signature : Scan.Schema MixedFlat.Field Unit, Trace signature}
    {window : MixedFlat.File.Window.Index input 0 input.len}
    (success : read limits input = .ok source)
    (indexed : MixedFlat.File.Window.readIndex limits.observation.ipc input 0 input.len = .ok window)
    (projection : Scan.Projection window.projectionSchema) (n : Nat) :
    ∃ same : source.1 = window.projectionSchema,
      let trace : Trace window.projectionSchema := same ▸ source.2
      match (trace.scan projection (fun _ => some true)).batches[n]? with
      | none => window.readProjectedAt limits n projection = .ok none
      | some event => ∃ output, window.readProjectedAt limits n projection = .ok (some output) ∧
          Agrees projection.schema output event :=
  Proofs.Formats.Arrow.MixedFlat.File.Events.read_projectedAt_scan success indexed projection n

end Silmaril.Formats.Arrow.MixedFlat.File.Events
