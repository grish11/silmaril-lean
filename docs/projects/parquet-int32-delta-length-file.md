# Bounded Parquet INT32 and delta-length BYTE_ARRAY source

`Silmaril.Formats.Parquet.Int32ByteArrayGroup.DeltaLength.File.Defs` exposes
`openFile`, `source` and `openSource` for one immutable checked Parquet
snapshot. Select the exact names of a required physical INT32 leaf and an
optional physical BYTE_ARRAY leaf in a flat schema. The output fields
follow that order and the binary slots carry opaque bytes.

The profile uses codec 0, data pages V1 with flat RLE levels or V2 with
flat levels, and actual page tags PLAIN (0) for INT32 and
DELTA_LENGTH_BYTE_ARRAY (6) for BYTE_ARRAY. It uses the checked group
reader's chunk association, framing and decoder limits, and inherits its
rejection of CRC-bearing pages, dictionary pages and other page kinds.
Payload validation covers the selected columns.

## Admission and trace

The file source reuses the checked PLAIN projection's structural admission
and total row cap with the same base limits as the selected group readers.
The checked footer equates the nonnegative file count to the sum of the
group counts. The cap is applied at open, before any page read.
`readAll_rowLimit` states this precedence and `readAll_rows_le` bounds
the rows emitted before EOS or a read error.

`readAll_trace` relates full consumption through `Reader.readAll` to the
exact original zero-based footer ordinals. `readAll_success` gives one
complete batch per group, including admitted empty groups.
`readAll_first_error` preserves the complete prior batches and the
original selected cause inside `Error.groupFailure`, including the group,
column, page ordinal and header byte offset of page errors.
`batch_projections` recovers the two positional columns from each batch.

## Fixtures and verification

The [row-group fixtures](parquet-int32-delta-length-group.md) independently
pin V1 and V2 with three 12-row groups, different page cuts in the two
columns, and an all-null binary page per group. The two V2 mutations fail
at group 1, column 1, page 2, header byte 760 with either actual tag 3 or
a truncated delta-length payload. A cap of 35 fails at open. A cap of 36
yields the exact 12-row prefix before either original error.

[The empty-middle fixture](../../data/parquet-int32-delta-length-file/delta-length-empty-middle-v2.parquet)
uses PyArrow 26.0.1 and Thrift 0.25.0. The oracle adds explicit zero-row
V2 frames to the producer's empty chunks, using the zero-count
delta-length stream from the pinned V2 all-null page. PyArrow reads the
same three groups before and after framing. The checked source emits
`[2, 0, 1]`. Changing the last group's binary page tag to 3 leaves
`[2, 0]` and reports group 2, column 1, page 0, header byte 95.

The empty-middle fixture SHA-256 is
`095df3ed224578be417cfec6a8acb3dc6f669a24c13f3b565552243018ca1e8e`.

```sh
fixture_tmp=$(mktemp -d)
python3 scripts/parquet-int32-delta-length-group/Oracle.py "$fixture_tmp/group"
diff -r data/parquet-int32-delta-length-group "$fixture_tmp/group"
python3 scripts/parquet-int32-delta-length-file/EmptyGroup.py "$fixture_tmp/delta-length-empty-middle-v2.parquet"
cmp data/parquet-int32-delta-length-file/delta-length-empty-middle-v2.parquet "$fixture_tmp/delta-length-empty-middle-v2.parquet"
lake build --wfail +Silmaril.Formats.Parquet.Int32ByteArrayGroup.DeltaLength.File.Tests
lake env lean -DautoImplicit=false -DwarningAsError=true tests/formats/parquet-int32-delta-length-file/Axioms.lean
```
