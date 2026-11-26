# Bounded whole-file INT32 and BYTE_ARRAY projection

`Int32ByteArrayGroup.File.openSource limits bytes int32 byteArray` checks
one plaintext Parquet snapshot and binds one named INT32 leaf and one named
BYTE_ARRAY leaf using the [one-group projection](parquet-int32-byte-array-group.md).
The caller supplies each field's exact name and required or optional
layout. The source schema puts INT32 first and BYTE_ARRAY second.
Its cells retain signed INT32 values and opaque `Bytes`, with empty byte
strings distinct from nulls. The result is a `Reader.OpenResult` for
the typed file source. [Definitions][defs]

Successfully opening the two bindings precedes the total-row check.
The source uses the admitted footer's total row count and rejects a file
above `maxFileRows` before any group callback. The inherited file, group,
page and value limits still apply. The selected chunks must use codec 0
and PLAIN tag 0 under the existing V1 RLE-level or V2 flat-level profiles.
The original footer ordinals form the cursor. Footer and schema validation
covers the file. The selected page walks examine only the two requested
chunks of each reached group.

Each successful callback yields one typed row per original pair. Consuming
the source gives one complete batch per successful group, including a
zero-row batch for a successfully decoded empty group. A read failure
keeps the exact prefix of earlier complete batches and retains the first
nested indexed cause in `.groupFailure index reason`. Within the group,
INT32 is read first. The source contract is independent of dataset
traversal, pruning, and IPC encoding.

## Lean contracts

- `File.openFile_snapshot` witnesses the one checked snapshot and its
  admitted total row count.
- `File.batch_projections` proves that both complete ordered slot lists
  are preserved and the batch has the pair count.
- `File.readAll_success` and `File.readAll_first_error` characterize the
  exact batches and outcome of consuming the source via `Reader.readAll`.
- `File.readAll_rows_le` bounds the sum of emitted batch row counts by
  `maxFileRows`, including on a read-error prefix. It uses
  `Footer.validate_rowCounts` and `Snapshot.check_rowCounts` to relate
  the validated total to the dense footer ordinals. These supporting
  laws reuse the existing validation and indexing functions.

[Theorem header][thms]

## Producer fixtures

The ordered reads reuse the four pinned Parquet V1/V2 fixtures from the
[BYTE_ARRAY file profile](parquet-plain-byte-array-file.md#independent-fixtures),
with Parquet Format **2.14.0** at
`04d56f291ff963e98bc37ab8100e2fc133ff583c`, PyArrow **26.0.1** and Thrift
**v0.25.0**. The clean files yield `[12, 12, 12]` rows per batch. The
INT32 page cuts `[8, 4]` and optional BYTE_ARRAY cuts `[4, 8]` already
differ within the group. The selected damaged column fails after the
first 12 rows with the same truncation at group 1, column 1, page 1,
header 608 for V1 or 646 for V2. Selecting the intact sibling reads
all 36 rows. A cap of 35 rejects the damaged file at open, while cap 36
preserves the selected page error. A double-damage control keeps the
same prefix and returns the original INT32 tag error.

The pinned [empty-middle-v2.parquet][empty] has SHA-256
`4417fe68ce84210af4979a2f7ef19d05764fc3ce3bf71f83b25b546658e76f48`.
PyArrow produced three groups of 3, 0 and 2 rows. It initially left the
empty chunks at offset zero with size zero. The Compact Thrift fixture
edit attaches one zero-row PLAIN V2 header with an empty body for each
selected leaf and updates the empty chunk metadata and PLAIN advertisement.
PyArrow reads the same groups before and after the edit. Lean observes
`[3, 0, 2]` at EOS and `[3, 0]` before a last-group tag failure at
group 2, column 1, page 0, header 108. [Empty-group oracle][oracle] ·
[Lean tests][tests]

```sh
fixture_tmp=$(mktemp -d)
python3 scripts/parquet-plain-byte-array-file/Oracle.py "$fixture_tmp/existing"
diff -r data/parquet-plain-byte-array-file "$fixture_tmp/existing"
python3 scripts/parquet-int32-byte-array-group/Check.py "$fixture_tmp/existing"
python3 scripts/parquet-int32-byte-array-file/EmptyGroup.py "$fixture_tmp/empty-middle-v2.parquet"
cmp data/parquet-int32-byte-array-file/empty-middle-v2.parquet "$fixture_tmp/empty-middle-v2.parquet"
lake build --wfail +Silmaril.Formats.Parquet.Int32ByteArrayGroup.File.Tests
make check CHECK_TARGETS='+Silmaril.Formats.Parquet.Int32ByteArrayGroup.File.Tests +Silmaril.Formats.Parquet.Int32ByteArrayGroup.Tests +Silmaril.Formats.Parquet.Plain.ByteArray.File.Tests parquet-flat-scan-regression parquet-page-regression'
lake env lean -DautoImplicit=false -DwarningAsError=true tests/formats/parquet-int32-byte-array-file/Axioms.lean
```

[defs]: ../../Silmaril/Formats/Parquet/Int32ByteArrayGroup/File/Defs.lean
[thms]: ../../Silmaril/Formats/Parquet/Int32ByteArrayGroup/File/Thms.lean
[tests]: ../../Silmaril/Formats/Parquet/Int32ByteArrayGroup/File/Tests.lean
[oracle]: ../../scripts/parquet-int32-byte-array-file/EmptyGroup.py
[empty]: ../../data/parquet-int32-byte-array-file/empty-middle-v2.parquet
