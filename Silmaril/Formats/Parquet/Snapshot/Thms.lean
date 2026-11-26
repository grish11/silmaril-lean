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

/-- A checked singleton footer and a successful group read yield one batch
followed by EOS, including when the decoded row list is empty. -/
theorem readAll_single {limits : Limits} {bytes : Bytes} {footer : Footer.Span}
    {metadata : Footer.Metadata} {group : Footer.RowGroup} {bind : Bind schema Value Failure}
    {decode : DecodeGroup schema Value Failure} {rows : Reader.RowGroup schema Value}
    (read : Footer.readFooter limits.footer bytes = .ok (footer, metadata))
    (valid : Footer.validate footer.start limits.maxSchemaDepth metadata = .ok ())
    (single : metadata.rowGroups = [group]) (bound : bind metadata = .ok decode)
    (decoded : ∀ snapshot, snapshot.bytes = bytes → snapshot.footer = footer →
      decode snapshot 0 group = .ok rows)
    (count : rows.length = group.numRows.toNat) :
    readAll limits bind bytes = .ok ⟨schema, ⟨[AlignedColumns.ofRows rows], .eos⟩⟩ :=
  Proofs.Formats.Parquet.Snapshot.readAll_single read valid single bound decoded count

end Silmaril.Formats.Parquet.Snapshot
