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

## Checks

```sh
lake build --wfail +Silmaril.Formats.Hive.Manifest.Checks
make check CHECK_TARGETS=+Silmaril.Formats.Hive.Manifest.Checks
lake build --wfail +Silmaril.Formats.Hive.Manifest.Pruning.Checks
make check CHECK_TARGETS=+Silmaril.Formats.Hive.Manifest.Pruning.Checks
```

The checks exercise original path spelling, canonical directories, repeated
declarations, an empty manifest and source, nullable predicates, path and
schema errors, prefix order, filtered open and read failures, early close,
and close failure. The pruning checks cover rejected failures and early
close, a retained failure, and ordered output with repeated paths.
[Manifest checks](../../Silmaril/Formats/Hive/Manifest/Checks.lean) ·
[Pruning checks](../../Silmaril/Formats/Hive/Manifest/Pruning/Checks.lean)
