module

public import Silmaril.Formats.Parquet.Snapshot.Defs
import Silmaril.Proofs.Formats.Parquet.Snapshot.Pull

public section

namespace Silmaril.Formats.Parquet.Snapshot

open Silmaril.Relational Silmaril.Formats.Arrow

variable {Id Kind Failure : Type*} {Value : Kind → Type*} {schema : Scan.Schema Id Kind}

/-- A checked byte snapshot has a successful close. Hitting the pull budget
observes that close, and a read that reaches a failed group preserves its
indexed error. A successful EOS still takes an additional pull. -/
theorem read_prefix_of_checked (limits : Limits) (bind : Bind schema Value Failure) (bytes : Bytes)
    (fuel : Nat) {snapshot : Checked} {decode : DecodeGroup schema Value Failure}
    (checked : check (Failure := Failure) limits bytes = .ok snapshot)
    (bound : bind snapshot.metadata = .ok decode) :
    (batchReader limits bind).read fuel bytes =
      let observed := Reader.denoteGroups (snapshot.readGroup decode) ((List.range snapshot.groupCount).take fuel)
      .ok ⟨schema, ⟨observed.1.map AlignedColumns.ofRows,
        match observed.2 with
        | .eos => if fuel ≤ snapshot.groupCount then .closed else .eos
        | termination => termination⟩⟩ :=
  Proofs.Formats.Parquet.Snapshot.read_prefix_of_checked limits bind bytes fuel checked bound

end Silmaril.Formats.Parquet.Snapshot
