# Write BinaryView IPC from one selected Parquet BYTE_ARRAY leaf

`Parquet.Plain.ByteArray.ToIpc.convert` takes immutable Parquet bytes,
one selected field name and required or optional layout, and separate
Parquet, IPC and view-column limits. It uses the checked file reader
for flat, uncompressed PLAIN BYTE_ARRAY Data Pages V1 and V2 in its
existing profile. The projection stays explicit even when the file
has other columns. The selected field becomes one BinaryView field
with its exact name and nullability. Present values remain opaque
octets. [Parquet reader profile](parquet-plain-byte-array-file.md) ·
[Arrow writer profile](arrow-binary-view.md)

The converter reads the entire selected column before emitting native
Arrow IPC V5. Each successfully exhausted footer group becomes one
ordered RecordBatch, including an admitted zero-row group. A source
with no footer groups produces a schema-only stream. Both streams
terminate with explicit EOS. `convert_readback` witnesses the original
indexed groups, the exact field, the batch and row counts, and the
nullable octets within each batch. It also gives their flattened table
observation. [Theorem header](../../Silmaril/Formats/Parquet/Plain/ByteArray/ToIpc/Thms.lean)

The pure result carries either complete stream bytes or the original
error tagged with its stage. Source admission and the first indexed
source read failure precede any writer error. The abstract Parquet
trace retains preceding complete groups even when a late source
failure prevents emission. The writer's original record index and
limit cause are available after successful source exhaustion.

## Independent checks

CPython 3.13.5, PyArrow 26.0.1, and Apache Thrift 0.25.0 check six
pinned Parquet inputs. PyArrow reads four actual Lean-emitted streams
and independently compares their V5 metadata, one-field schema,
footer-ordered batch sizes, nullable octets, and final EOS.

| Source | Expected batch sizes |
| --- | --- |
| Optional PLAIN V2 from column ordinal 1 | `[4, 4]` |
| Required PLAIN V1 | `[12, 12, 12]` |
| Schema-only Parquet | `[]` |
| Framed zero-row V2 group | `[0]` |

The zero-row group fixture uses an original in-file Data Page V2
header at byte 4. PyArrow independently reads that group. A separate
PyArrow-produced zero-row group with page offsets of zero is rejected
by the checked Parquet footer. The late source control changes the
length word at byte 162 and reports group 1, column 1, page 0, header
byte 136 with an unchanged first group. Writer controls cover a
12-byte value limit and an IPC batch-count limit.
[Fixture hashes](../../scripts/parquet-byte-array-to-ipc-oracle/sha256.json)

```sh
lake build --wfail +Silmaril.Formats.Parquet.Plain.ByteArray.ToIpc.Checks +Silmaril.Formats.Parquet.Plain.ByteArray.ToIpc.Source.Checks
python3.13 -B scripts/parquet-byte-array-to-ipc-oracle/check.py --out /tmp/parquet-byte-array-to-ipc
```

[Parquet Format 2.14.0 encodings](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/Encodings.md) ·
[Arrow 26.0.1 BinaryView and IPC](https://github.com/apache/arrow/blob/9e5d6978e9acf372cc989aaaf94e863fe8582c90/docs/source/format/Columnar.rst)
