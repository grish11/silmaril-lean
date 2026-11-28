module

public import Silmaril.Formats.Parquet.Reader.Defs
import Silmaril.Proofs.Formats.Parquet.Reader.Pull

public section

namespace Silmaril.Formats.Parquet.Reader

open Silmaril.Relational Silmaril.Formats.Arrow

variable {Input Group Id Kind Error : Type*} {Value : Kind → Type*} {schema : Scan.Schema Id Kind}

/-- A bounded pull observes one batch per successful attempted group.
After the last budgeted pull it closes the unread suffix. EOS needs an
additional pull, and a failed read terminates with that exact error. -/
theorem read_prefix_opened (openInput : Input → OpenResult Group Id Value Error) (input : Input)
    (fuel : Nat) {source : Source Group schema Value Error} (opened : openInput input = .ok ⟨schema, source⟩) :
    (batchReader openInput).read fuel input =
      let observed := denoteGroups source.readGroup (source.groups.take fuel)
      .ok ⟨schema, ⟨observed.1.map AlignedColumns.ofRows,
        match observed.2 with
        | .eos =>
          if fuel ≤ source.groups.length then
            match source.close (source.groups.drop fuel) with
            | .ok () => .closed
            | .error error => .closeError error
          else .eos
        | termination => termination⟩⟩ :=
  Proofs.Formats.Parquet.Reader.read_prefix_opened openInput input fuel opened

end Silmaril.Formats.Parquet.Reader
