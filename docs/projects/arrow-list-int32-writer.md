# Native Arrow IPC writer for nullable List<Int32>

`Arrow.ListInt32.Stream.Writer.emit` writes a complete little-endian
modern V5 IPC stream with one nullable List field and one nullable
signed Int32 child. The caller supplies the parent and child names and
the ordered batches. A cell is `Option (List (Option Int32))`, so null
lists, empty lists and null children remain distinct. A zero-row batch
still emits a RecordBatch. An empty batch sequence emits the Schema
and EOS.
[Pinned Arrow schema IDL](https://github.com/apache/arrow/blob/9e5d6978e9acf372cc989aaaf94e863fe8582c90/format/Schema.fbs) · [Pinned Arrow IPC and columnar format](https://github.com/apache/arrow/blob/9e5d6978e9acf372cc989aaaf94e863fe8582c90/docs/source/format/Columnar.rst)

The writer reuses the V5 Message prefix, primitive Int32 child
fragment, common record metadata writer, and aligned buffer packer.
The new List field fragment supplies the empty List type table and
its singleton child vector. Both field names are UTF-8 strings.
The parent and child validity bits use least-significant-bit order.
Offsets start at zero and sum the lengths of preceding present
lists. Null lists have zero-length physical spans and the final
offset equals the total child length. Null children use a zero
physical word and a clear child validity bit. The two field nodes
carry the exact parent and child lengths and null counts. The four
descriptors are in depth-first order. Lengths exclude zero padding
to the next eight-byte boundary. An empty record has a single zero
offset and no parent bits or child slots.

The writer checks stream batch, parent-row, and child-slot budgets,
then checks per-record limits and signed wire ranges before
allocating the physical buffers. It writes one exact EOS after the
records. A successful `emit` also checks the complete carrier with
the native LIST reader under the same limits. Success certifies the
two field names, every ordered batch and every child count. The
canonical writer works in memory and is opt-in. Existing writers
keep their current profiles. Composition with the Parquet LIST
event source is a separate change.
[Reader contract](arrow-list-int32-stream.md) · [Writer API and proofs](../../Silmaril/Formats/Arrow/ListInt32/Stream/Writer/Thms.lean)

`offsetWords_at` identifies each offset with its input prefix.
`offsetWords_signed` connects every offset to the signed wire
domain after preflight. `pack_exact`, `metadata_exact` and
`emitRecord_exact` account for the original logical buffer bytes,
record metadata, node counts and exact padded body extent.
`emit_wire` identifies the schema, ordered frames and EOS.
`emit_readback` gives the certified reader's ordered nullable
values, batch boundaries, child totals and checked frame chain
through EOS.

## Independent readback

Lean emits a four-batch stream and a schema-only stream. Pinned
PyArrow 26.0.1 validates and reads both. The oracle checks the UTF-8
names and both nullability flags, record boundaries, original node
and buffer descriptors, bitmap octets, offsets, signed child words,
zero padding and exact EOS. The multi-batch stream covers null and
empty lists, nullable children, both signed INT32 endpoints, a
zero-row batch, and an all-null batch. Lean examples also check
empty field names and typed refusals for signed offset and body
overflow and each configured budget.
[Output hashes and wire observations](../../scripts/arrow-list-int32-writer/observations.txt) · [PyArrow wheel pin](parquet-column-index.md#pinned-independent-fixture)

```sh
set -o pipefail
replay=$(mktemp -d)
lake build --wfail +Silmaril.Formats.Arrow.ListInt32.Stream.Writer.Examples
make check CHECK_TARGETS=+Silmaril.Formats.Arrow.ListInt32.Stream.Writer.Examples
python3 scripts/arrow-list-int32-writer/Oracle.py "$replay" |
  diff -u scripts/arrow-list-int32-writer/observations.txt -
```
