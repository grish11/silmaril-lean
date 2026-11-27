module

public import Silmaril.Formats.Arrow.MixedFlat.File.Events.Pull.Defs
public import Mathlib.Data.List.Forall2
import Silmaril.Proofs.Formats.Arrow.MixedFlat.File.Events.Pull.Laws

public section

namespace Silmaril.Formats.Arrow.MixedFlat.File.Events.Pull

open Silmaril.Relational

/-- Exhaustion through EOS gives the same schema and exact ordered event
batches as the eager strict file reader. -/
theorem readAll_eager {limits : MixedFlat.Limits} {input : KBytes}
    {source : Σ signature : Scan.Schema MixedFlat.Field Unit, Trace signature} :
    (readAll limits input = .ok source ∧ source.2.termination = .eos) ↔
      MixedFlat.File.Events.read limits input = .ok source :=
  Proofs.Formats.Arrow.MixedFlat.File.Events.Pull.readAll_eager

/-- A terminal read failure observes precisely the completed footer prefix.
The next entry supplies the original decoder cause or the running budget
error at the same ordinal that the eager reader reports. -/
theorem readAll_failure_exact {limits : MixedFlat.Limits} {input : KBytes}
    {source : Σ signature : Scan.Schema MixedFlat.Field Unit, Trace signature} {error : MixedFlat.File.Events.Error}
    (read : readAll limits input = .ok source) (failed : source.2.termination = .readError error) :
    ∃ index : MixedFlat.File.Index input,
      MixedFlat.File.readIndex limits.observation.ipc input = .ok index ∧
      source.1 = schema index.footer.fields ∧
      ∃ completed block rest observed,
        index.footer.blocks = completed ++ block :: rest ∧
        completed.mapM (MixedFlat.File.readRecord limits input index.footer.fields) = .ok observed ∧
        List.Forall₂ (Agrees source.1) observed source.2.batches ∧
        StopsAt limits input index.footer.fields completed.length
          (observed.map MixedFlat.Observed.rowCount).sum block error ∧
        MixedFlat.File.Events.read limits input = .error error :=
  Proofs.Formats.Arrow.MixedFlat.File.Events.Pull.readAll_failure_exact read failed

end Silmaril.Formats.Arrow.MixedFlat.File.Events.Pull
