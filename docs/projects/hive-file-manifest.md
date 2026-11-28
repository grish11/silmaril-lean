# Declared Hive file manifests

`prepare` takes a list of relative file declarations, a physical scan
schema, a typed Hive partition schema, the Hive path options and a checked
text converter. It returns a file entry for each declaration in list order.
Repeated declarations remain repeated. It checks the schema even for an
empty list, then reports the first invalid declaration before scanning.
[Executable API](../../Silmaril/Formats/Hive/Manifest/Defs.lean)

## Paths and bindings

| Stage | Contract |
| --- | --- |
| Split | Split using literal slashes. The final component is the filename. Reject an absent filename, empty or dot/dot-dot components, literal backslashes or NUL, and colons in the filename. A bare filename is at the dataset root. This is a lexical convention for declared paths. |
| Parse and normalize | Parse the parent using the Hive directory codec, then render its canonical escaped directory in the declared key order. The filename is opaque, including percent sequences and equals signs. |
| Convert | Reuse the typed Hive schema and binding checks, including collision, unknown-key, missing-key, duplicate-key, null and conversion policies. The prepared file carries a typed nullable partition tuple. |
| Open identifier | Give the opener the original declaration, including its directory and filename spelling. The canonical directory describes the logical partition and does not rewrite the file identifier. |

[`PartitionPath`](hive-partition-path.md) · [Typed Hive bindings](hive-typed-partitions.md)

## Scan and failures

`scan` takes a pure opener. At each reached file, the opener either reports a
failure or returns a typed Parquet source and pull budget. The virtual tuple
controls filtering and projection through the [Parquet Arrow scan](hive-parquet-scan.md).
The scan calls the opener for the first file and advances only after EOF.
It returns an Arrow trace at the projected schema.

An open failure is represented as a dataset read error with an explicit
`FileError.open` cause. Source read and close errors carry the original path
and payload in `FileError.source`, with the Arrow terminal variant retained.
An open error produces no rows for that file. A read or close failure retains
the selected rows already emitted by the file. Early close stops traversal and
retains its prefix. Full exhaustion emits EOF. False and unknown partition
predicates suppress rows while keeping these outcomes.

`prepare_preserves_paths` proves that successful preparation preserves
original opener inputs in order. `scan_open_failure` gives the exact
observation when the current file fails to open. `scan_first_terminal`
proves that the first non-EOF file contributes its selected prefix and
terminal outcome after all earlier selected rows. Later entries do not
affect this observation.
[Theorem header](../../Silmaril/Formats/Hive/Manifest/Thms.lean)

The opener and source functions are pure. Filesystem discovery, real I/O and
byte decoding are outside this layer.

## Partition pruning

`scan` is the error-preserving reference. It opens every reached declaration
and observes the terminal outcome even for a filtered file.
The opt-in `scanSkippingRejected` evaluates the partition predicate before
opening a reached file. False and unknown skip the open and let traversal
continue. Retained declarations keep their order, including duplicates, and
use the same reader and pull budget as the reference. [Pruning API](../../Silmaril/Formats/Hive/Manifest/Pruning/Defs.lean)

`RejectedFilesReachEOF` requires every rejected declaration to reach EOF in
the reference scan under that file's supplied budget. Successful open alone
leaves read and close outcomes unknown. A file can yield its last batch and
still close early if the budget leaves no pull to observe EOF. Retained files
can fail under this contract. `scanSkippingRejected_eq_scan` proves equality
of traces under the contract, and `scanSkippingRejected_equivalent` gives
equality of Arrow observations. [Pruning theorems](../../Silmaril/Formats/Hive/Manifest/Pruning/Thms.lean)

For a rejected singleton with a non-EOF outcome,
`scanSkippingRejected_not_equivalent_singleton` proves that the policies
disagree. In the regression, a rejected file opens and emits a group before a
read failure. The reference returns the earlier selected rows and the error.
Skipping opens continues to a later selected file and reaches EOF.

## One budget across checked snapshots

[`scanSnapshotsBounded`](../../Silmaril/Formats/Hive/Manifest/ParquetSnapshot/Bounded/Defs.lean)
scans a prepared Hive manifest over supplied immutable Parquet snapshots.
A single caller-supplied budget counts logical actions across all file
occurrences, including repeated declarations and filtered partitions.

| Action | Charge |
| --- | --- |
| Attempt lookup by literal path and checked open with the declared schema | 1 together |
| Attempt to pull one row group, including an empty group or a failed read | 1 |
| Pull after the final group to observe file EOS | 1 |
| Dispose of an immutable snapshot on budget exhaustion | 0 |

A manifest with no remaining entries yields EOS even at budget zero. At
zero budget with another entry pending, the scan returns `.closed` before
lookup. After opening a file it must observe that file's EOS before advancing,
including a file with no groups. If the last group used the last action,
the scan returns `.closed` with the emitted prefix. A reached failure stops
the scan and retains its original path and typed cause, including a group
index when applicable. Filtering suppresses batches while preserving
charges and reached outcomes.

The output preserves literal manifest occurrence order, row-group batch
boundaries for retained partitions, stable row order within each batch, and
duplicate rows. Projection operates on the typed augmented schema and
preserves row count with zero output columns. The budget measures logical
attempts. Existing reader limits govern admission and decoding within individual
actions. The API operates on supplied snapshots and performs no filesystem IO.

[`scanSnapshotsBounded_eq_reference`](../../Silmaril/Formats/Hive/Manifest/ParquetSnapshot/Bounded/Thms.lean)
proves exact trace equality to an independent reference that denotes the
affordable row-group prefix of each checked source, constructs projected
batches from those typed rows, and debits the explicit EOS before moving on.

[Bounded checks](../../Silmaril/Formats/Hive/Manifest/ParquetSnapshot/Bounded/Checks.lean)
reuse the [pinned two-group PyArrow V1 and V2 files](parquet-flat-scan.md#independent-fixtures)
and the late V2 failure at byte 234 documented in [Hive write planning](hive-write-plan.md#planning-from-a-checked-snapshot-scan).
The additional [422-byte zero-group file](../../tools/parquet-flat-scan/fixtures/flat-empty-no-groups.parquet)
has SHA-256 `69b2b6e2c21df0ba477c3d218c2dc9ff09a87a5f10ed0f029d16c669457813ec`.
To regenerate it, use the CPython 3.14.7 image and hash-pinned PyArrow 26.0.1
and NumPy 2.5.5 wheels from the [Hive oracle recipe](hive-write-plan.md#pinned-checks)
and run the following in an output directory.

```python
import pyarrow as pa
import pyarrow.parquet as pq

schema = pa.schema([
    pa.field("required_i32", pa.int32(), nullable=False),
    pa.field("optional_i32", pa.int32(), nullable=True),
])
name = "flat-empty-no-groups.parquet"
with pq.ParquetWriter(name, schema, compression="NONE", use_dictionary=False, write_statistics=False):
    pass
actual = pq.ParquetFile(name)
assert actual.num_row_groups == actual.metadata.num_rows == 0
assert actual.schema_arrow.equals(schema)
assert actual.read().equals(schema.empty_table())
```

### Agreement with the strict full scan

[`SnapshotScanCost`](../../Silmaril/Formats/Hive/Manifest/ParquetSnapshot/Bounded/Defs.lean)
witnesses a logical action count directly from the literal occurrence list
and checked sources. A successful occurrence supplies evidence that all
its groups decode in order. It costs the group count plus two, for checked
open and EOS, before charging the rest of the manifest. A failed open
costs one action, including when lookup fails. An opened file that fails
after `k` successful groups costs `k + 2`, for open, those group pulls,
and the failed pull. Both failure cases stop at the first failed action
and require no evidence about any later file. The read failure also
requires no evidence about later groups. No remaining occurrences cost
zero actions.

[`snapshotScanCost_exists`](../../Silmaril/Formats/Hive/Manifest/ParquetSnapshot/Bounded/Thms.lean#L42)
constructs a witness for every finite supplied manifest and checked opener
input, including failed opens and partial reads.
[`scanSnapshotsBounded_eq_scan_of_cost`](../../Silmaril/Formats/Hive/Manifest/ParquetSnapshot/Bounded/Thms.lean#L30)
shows that any budget at least the witnessed cost returns exactly the
unbounded strict snapshot trace, including projected batch boundaries,
ordered nullable cells, and the terminal outcome. The witness uses group
reads independently of projection and partition selection. Filtered
occurrences still spend actions and preserve every reached failure.

The [cost regressions](../../Silmaril/Formats/Hive/Manifest/ParquetSnapshot/Bounded/Checks.lean)
compare both APIs on the same pinned fixtures with explicit budgets and
include a checked footer rejection after a successful occurrence. One
action below the successful boundary can emit all rows and still return
`.closed`. The law is a proof about pure snapshots and logical actions.

### Exact cutoff and appended occurrences

[`scanSnapshotsBounded_exact_boundary`](../../Silmaril/Formats/Hive/Manifest/ParquetSnapshot/Bounded/Thms.lean)
gives the other side of the budget law. For a witnessed cost, the immutable
snapshot scan returns `.closed` exactly when its budget is smaller than
that cost. Its emitted aligned batches are always an ordered prefix of
the strict trace, including duplicates, nullable cells, and explicit
batch row counts at zero output width. Combined with sufficient-budget
agreement, the cutoff also determines the unique cost for that manifest
and checked input. A scan can have emitted its last batch while still
needing an action to observe EOS.

[`scanSnapshotsBounded_append_of_stopped`](../../Silmaril/Formats/Hive/Manifest/ParquetSnapshot/Bounded/Thms.lean)
preserves the exact trace when later literal occurrences are appended
after a scan that returned `.closed` or an error. A scan that has
observed manifest EOS may have enough budget to reach appended entries
and observe their outcomes. The laws concern trace observations of
supplied immutable snapshots at a logical action budget.

The bounded checks enumerate budgets below, at, and above the witnessed
boundary for empty, repeated, zero-width, and damaged inputs. They also
compare appended suffixes at close and failure, with an EOS control in
which the appended entry is reached.

## Checks

```sh
lake build --wfail +Silmaril.Formats.Hive.Manifest.Checks
make check CHECK_TARGETS=+Silmaril.Formats.Hive.Manifest.Checks
lake build --wfail +Silmaril.Formats.Hive.Manifest.Pruning.Checks
lake build --wfail +Silmaril.Formats.Hive.Manifest.ParquetSnapshot.Bounded.Checks
make check CHECK_TARGETS=+Silmaril.Formats.Hive.Manifest.Pruning.Checks
```

The checks exercise original path spelling, canonical directories, repeated
declarations, an empty manifest and source, nullable predicates, path and
schema errors, prefix order, filtered open and read failures, early close,
and close failure. The pruning checks cover rejected failures and early
close, a retained failure, and ordered output with repeated paths.
[Manifest checks](../../Silmaril/Formats/Hive/Manifest/Checks.lean) ·
[Pruning checks](../../Silmaril/Formats/Hive/Manifest/Pruning/Checks.lean)
