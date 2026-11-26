module

public import Silmaril.Formats.Parquet.Snapshot.Defs
import all Silmaril.Formats.Parquet.Snapshot.Defs
import Silmaril.Formats.Parquet.Reader.Pull.Thms

public section

namespace Silmaril.Proofs.Formats.Parquet.Snapshot

open Silmaril.Formats Silmaril.Formats.Parquet Silmaril.Formats.Parquet.Snapshot
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
        | termination => termination⟩⟩ := by
  have opened : (openSource limits bind bytes).map (fun source => ⟨schema, source⟩) =
      .ok (⟨schema, snapshot.source decode⟩ : Σ s, Reader.Source Nat s Value (Error Failure)) := by
    simp [openSource, checked, bound, Except.map]
  unfold batchReader
  rw [Reader.read_prefix_opened _ bytes fuel opened]
  simp [Checked.source]
  cases (Reader.denoteGroups (snapshot.readGroup decode) (List.range (min fuel snapshot.groupCount))).2 <;> rfl

end Silmaril.Proofs.Formats.Parquet.Snapshot
