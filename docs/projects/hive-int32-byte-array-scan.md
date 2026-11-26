# Hive manifests with selected INT32 and BYTE_ARRAY columns

[`Manifest.int32ByteArraySnapshotOpener`](../../Silmaril/Formats/Hive/Manifest/ParquetSnapshot/Int32ByteArray/Defs.lean)
opens immutable Parquet bytes by their literal manifest path. It binds a
named INT32 leaf and a named opaque BYTE_ARRAY leaf using the
[checked paired file source](parquet-int32-byte-array-file.md). The physical
output schema is the selected pair in INT32 then BYTE_ARRAY order, with the
declared names and required or optional layouts checked by the source.
A present empty byte sequence remains distinct from null.

## Admission and observation

1. Use the existing [manifest preparation](hive-file-manifest.md) for
   relative paths and typed partition conversion. Explicit null markers,
   omitted fields and converter errors retain their existing policies.
2. The opener attempts the literal lookup, then performs one checked
   Parquet open and pair bind. It inspects all flat physical leaf names from
   that same open before any group read. The first name in physical leaf
   order reserved by the partition schema is an open error, including
   names on unselected siblings. The root schema node is excluded. Other
   siblings follow the checked source's flat schema admission.
3. Feed the source to the strict manifest scan. Visit literal occurrences
   in supplied order, including duplicates. For each retained group,
   attach the typed virtual cells in declared order after the physical
   pair, then apply the requested logical projection. False and unknown
   partition predicates suppress output batches. They preserve reached
   lookup, open and group-read failures. Logical projection still observes
   the outcome of reading both selected physical leaves.

A successful retained empty group contributes a zero-row batch. A
zero-width logical projection retains the row count of every retained
batch. The first failed open or group ends traversal and retains the
selected prefix, including completed groups of the failing file. Its
error carries the original literal path and the Parquet payload unchanged
inside the Hive error wrappers.

[`Manifest.scanInt32ByteArraySnapshots_eq_reference`](../../Silmaril/Formats/Hive/Manifest/ParquetSnapshot/Int32ByteArray/Thms.lean)
proves exact trace equality with an independent ordered group fold. The
fold shares checked file admission and the typed source, denotes its
groups directly, and projects materialized rows before building aligned
batches. `scanInt32ByteArraySnapshots_collect_eq_rows` gives the
corresponding ordered row and terminal observation.

## Logical action budget

[`scanInt32ByteArraySnapshotsBounded`](../../Silmaril/Formats/Hive/Manifest/ParquetSnapshot/Int32ByteArray/Bounded/Defs.lean)
uses the common [bounded manifest traversal](hive-file-manifest.md#one-budget-across-checked-snapshots)
with this checked opener. Charge one action per attempted literal open,
one per group pull, and one for the explicit file EOS pull. Each repeated
path is charged independently. A filtered partition still consumes its
actions and preserves its reached failure.

[`Int32ByteArrayScanCost` and its laws](../../Silmaril/Formats/Hive/Manifest/ParquetSnapshot/Int32ByteArray/Bounded/Thms.lean)
witness the actions through manifest EOS or the first reached failure for
every prepared manifest. The scan returns `.closed` exactly below that
cost. At any budget its aligned batches form an ordered prefix of the
full trace. A sufficient budget gives the exact existing mixed manifest denotation. An empty batch
costs one group pull and keeps its boundary even at zero projected width.
An empty manifest reaches EOS with zero actions. The budget measures
these logical actions over supplied immutable snapshots.

## Fixtures

[Lean checks](../../Silmaril/Formats/Hive/Manifest/ParquetSnapshot/Int32ByteArray/Checks.lean)
reuse the existing [pinned PyArrow V1/V2 byte-array files](parquet-plain-byte-array-file.md#independent-fixtures)
and [empty-middle file](parquet-int32-byte-array-file.md#producer-fixtures).
The existing producer recipes give exact hashes and PyArrow and Thrift
provenance. The checks cover an escaped literal partition, a default
marker, an omitted key, repeated files, repeated projected columns,
and `[3, 0, 2]` batches at full and zero output width. An unselected
`key` leaf triggers the reserved-name error after an earlier file has
succeeded. The V2 damaged payload retains the exact group, column, page
and header position after prefix rows, including with partition filtering
or zero-width output. The reserved-name policy and literal occurrence
order are checked by Lean.

```sh
lake build --wfail +Silmaril.Formats.Hive.Manifest.ParquetSnapshot.Int32ByteArray.Checks
make check CHECK_TARGETS=+Silmaril.Formats.Hive.Manifest.ParquetSnapshot.Int32ByteArray.Checks
```
