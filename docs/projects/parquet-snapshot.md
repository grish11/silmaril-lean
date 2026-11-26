# Checked Parquet snapshots as Arrow sources

`Snapshot.check` reads a plaintext footer from one immutable `Bytes` value,
and applies the existing metadata, interval, schema-depth and row-count
validation. The checked value retains those same bytes, the footer span and a
dense, zero-based row-group index in footer order. Bounds and semantic checks
follow the [Parquet footer profile](parquet-footer.md). [Source API](../../Silmaril/Formats/Parquet/Snapshot/Defs.lean)

`openSource` takes a `Bind` capability at the requested typed scan schema.
It checks the validated metadata and returns a `DecodeGroup` closure. This
closure can retain the schema plan and decoder-specific limits. A call
receives the checked snapshot, the group ordinal and its footer descriptor.
The snapshot adapter verifies the number of rows returned before Arrow sees a
batch. The capability supplies the physical decoding and schema interpretation.

A failed footer or schema check prevents schema emission. An out-of-range
index, a decoder error or a count mismatch carries the group ordinal. Pulls
visit one group at a time, preserving footer order. A successful group yields
one batch, including an empty batch for an empty group. A read failure
consumes the cursor and preserves the earlier batches. EOF consumes the
exhausted cursor. Early close drops the unread suffix without calling the
decoder. For immutable in-memory bytes, close has no cleanup failure. These
are the abstract Arrow reader's lifetime rules. [Arrow event API](../../Silmaril/Formats/Arrow/Events/Defs.lean)

`Manifest.snapshotOpener` uses the original declared path to look up a
snapshot, wraps lookup errors separately, and supplies one pull beyond the
group count so the manifest can observe EOF. The existing strict manifest
scan retains file order and repeated declarations, and stops after the first
open or read failure. File discovery and I/O are outside this pure interface.
[Hive opener](../../Silmaril/Formats/Hive/Manifest/ParquetSnapshot/Defs.lean)

The theorem header shows that each successful read returns the indexed
decoder's rows at the footer's declared count. A full EOF observation is
exactly ordered concatenation of successful group observations. The first
indexed failure keeps exactly the successful prefix and is independent of the
later groups. These laws concern the supplied decoder's observations.
[Theorem header](../../Silmaril/Formats/Parquet/Snapshot/Thms.lean)

## Fixture and checks

The regression embeds 353 bytes generated and independently read by [PyArrow
26.0.1](https://pypi.org/project/pyarrow/26.0.1/). The SHA-256 is
`9fee242f1ebc1b23b75e8fe11e2dc54d758b3859aa181ad86056fe9e722a4b50`.
The test capability reads each single-page chunk with `Page.readChunk` and
passes its V1 body and header fields to `ScalarPage.decode .int32`. The body
spans `[23,37)`, `[56,70)` and `[89,99)` agree with Apache Thrift v0.25.0.
Production assembly across pages and columns remains part of the supplied
capability. [Page framing](parquet-page-framing.md) ·
[Scalar page profile and tool pins](parquet-scalar-page.md)

```python
import pyarrow as pa
import pyarrow.parquet as pq

table = pa.table({"value": pa.array([11, 12, 21, 22, 31], type=pa.int32())})
pq.write_table(table, "snapshot-int32.parquet", row_group_size=2,
               use_dictionary=False, compression="NONE", write_statistics=False,
               store_schema=False)
file = pq.ParquetFile("snapshot-int32.parquet")
assert file.read().equals(table)
assert [file.metadata.row_group(i).num_rows for i in range(file.num_row_groups)] == [2, 2, 1]
```

```sh
lake build --wfail +Silmaril.Formats.Parquet.Snapshot.Checks
make check CHECK_TARGETS=+Silmaril.Formats.Parquet.Snapshot.Checks
```

The checks cover real footer opening and bounded INT32 slices, early close,
lookup and schema rejection, indexed read failure, count mismatch, and Hive
file order with repeated declarations. [Lean checks](../../Silmaril/Formats/Parquet/Snapshot/Checks.lean)
