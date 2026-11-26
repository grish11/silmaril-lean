module

public import Silmaril.Formats.Parquet.Snapshot.Defs
import Silmaril.Proofs.Formats.Parquet.Snapshot.Correctness

public section

namespace Silmaril.Formats.Parquet.Snapshot

open Silmaril.Relational Silmaril.Formats.Arrow

variable {Id Kind Failure : Type*} {Value : Kind → Type*} {schema : Scan.Schema Id Kind}

/-- A successful indexed read returns exactly the decoder's rows at the
footer's declared count. -/
theorem Checked.readGroup_ok_iff (snapshot : Checked) (decode : DecodeGroup schema Value Failure)
    (index : Nat) (rows : Reader.RowGroup schema Value) :
    snapshot.readGroup decode index = .ok rows ↔ ∃ group,
      snapshot.groupAt index = some group ∧ decode snapshot index group = .ok rows ∧
        rows.length = group.numRows.toNat :=
  Proofs.Formats.Parquet.Snapshot.readGroup_ok_iff snapshot decode index rows

/-- Successful full consumption observes the concatenation in footer order. -/
theorem Checked.collect_readAll_success (snapshot : Checked) (decode : DecodeGroup schema Value Failure)
    (groups : List (Reader.RowGroup schema Value))
    (decoded : (List.range snapshot.groupCount).mapM (snapshot.readGroup decode) = .ok groups) :
    (snapshot.readAll decode).collect = .ok ⟨⟨schema, groups.flatten⟩, .eos⟩ :=
  Proofs.Formats.Parquet.Snapshot.collect_readAll_success snapshot decode groups decoded

/-- An EOF observation certifies successful reads of all footer indices and
contains exactly the concatenated rows of those reads. -/
theorem Checked.collect_readAll_eof (snapshot : Checked) (decode : DecodeGroup schema Value Failure)
    (observation : Events.Observation Id Value (Error Failure))
    (collected : (snapshot.readAll decode).collect = .ok observation)
    (eof : observation.termination = .eos) :
    ∃ groups, (List.range snapshot.groupCount).mapM (snapshot.readGroup decode) = .ok groups ∧
      observation = ⟨⟨schema, groups.flatten⟩, .eos⟩ :=
  Proofs.Formats.Parquet.Snapshot.collect_readAll_eof snapshot decode observation collected eof

/-- The first failed read retains exactly the earlier rows and determines the
terminal payload independently of all later groups. -/
theorem Checked.collect_readAll_first_error (snapshot : Checked) (decode : DecodeGroup schema Value Failure)
    (before after : List Nat) (index : Nat) (groups : List (Reader.RowGroup schema Value))
    (error : Error Failure) (split : List.range snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (snapshot.readGroup decode) = .ok groups)
    (failed : snapshot.readGroup decode index = .error error) :
    (snapshot.readAll decode).collect = .ok ⟨⟨schema, groups.flatten⟩, .readError error⟩ :=
  Proofs.Formats.Parquet.Snapshot.collect_readAll_first_error snapshot decode before after index groups
    error split earlier failed

end Silmaril.Formats.Parquet.Snapshot
