# Native Arrow IPC stream for nullable List<Int32>

`Arrow.ListInt32.Stream.read` observes a little-endian, modern-framed
V5 IPC stream with one nullable Arrow `List` field and one nullable
signed Int32 child. It retains both original field names. The schema
uses List union tag 12, its empty payload table and exactly one child
field. The shared FlatBuffers schema parser checks the primitive child.
Schema features, custom metadata, dictionaries and compressed records
are outside this profile.
[Pinned Arrow 26.0.1 schema IDL](https://github.com/apache/arrow/blob/9e5d6978e9acf372cc989aaaf94e863fe8582c90/format/Schema.fbs) · [Pinned Arrow IPC and columnar format](https://github.com/apache/arrow/blob/9e5d6978e9acf372cc989aaaf94e863fe8582c90/docs/source/format/Columnar.rst)

A record has two field nodes and four aligned, bounded descriptors in
depth-first order: parent validity, parent offsets, child validity
and child values. Parent node length equals the record row count.
Both declared null counts must match the corresponding bitmap bits.
A missing bitmap represents all-valid slots. Unused bits, bytes after
a bitmap's logical range, and ordinary body padding carry no observed
values. The child reader uses the shared little-endian signed INT32
decoder.

The parent offset buffer has exactly one signed nonnegative 32-bit
word per row plus the final word. This profile requires normalized
endpoints, with first offset zero and final offset equal to the child
length. Adjacent offsets are nondecreasing and bounded for every
parent, including null parents. A null parent can cover a nonempty
child span. Its original child slots are checked and charged to the
budget, while its observed value is null. Equal offsets for a valid
parent denote an empty list. Individual child nulls are preserved.
A zero-row record has its own frame, with a single zero offset and no
child slots.

The observer returns one batch per record in original order, each
with its absolute offset, metadata length, body length, child count
and nullable rows. Its typed row is `Option (List (Option Int32))`.
Stream budgets cap batch count, cumulative rows and cumulative physical
child slots. Metadata and body bounds use the shared IPC limits.
Modern EOS must end the carrier exactly. On an invalid stream the
observer returns a typed error, indexed at the record or expected EOS
where applicable.

`readRows_wire` ties the exact counts and ordered parent and child
slots to the original buffers. `record_ranges` proves exact original
metadata and body sub-slices. `read_wire` traces the schema and every
batch through exact EOS. `batches_length_le` includes empty records in
the batch budget.
[Public API and theorems](../../Silmaril/Formats/Arrow/ListInt32/Stream/Thms.lean)

The default flat reader retains its previous profile. Other nested
types, Arrow IPC files, LIST serialization, and composition with the
Parquet LIST event source are outside this reader increment.

## Native fixture

Pinned PyArrow 26.0.1 emits three record batches, including an empty
batch. The first batch distinguishes null, empty, null children and
present signed values, including a physical child masked by a null
parent. The last batch has omitted validity buffers and both signed
INT32 endpoints. PyArrow rereads the native stream and the comparator
independently inspects the producer's FlatBuffers nodes, descriptors,
bitmaps, offsets, child words, frame extents and EOS. Lean checks the
exact observations and refuses malformed offsets, validity counts,
descriptors, wrong child width, truncated frames, missing or trailing
EOS and exhausted budgets.
[Fixture and mutation observations](../../scripts/arrow-list-int32-stream/observations.txt) · [PyArrow wheel pin](parquet-column-index.md#pinned-independent-fixture)

```sh
set -o pipefail
replay=$(mktemp -d)
python3 scripts/arrow-list-int32-stream/Oracle.py "$replay/nullable-list-int32.arrows" |
  diff -u scripts/arrow-list-int32-stream/observations.txt -
cmp data/arrow-list-int32-stream/nullable-list-int32.arrows "$replay/nullable-list-int32.arrows"
lake build --wfail +Silmaril.Formats.Arrow.ListInt32.Stream.Examples
make check CHECK_TARGETS=+Silmaril.Formats.Arrow.ListInt32.Stream.Examples
```
