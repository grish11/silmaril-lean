# Canonical nullable INT32 LIST file source

`ListFile.openFile` admits a plaintext snapshot with a single optional
three-level LIST column. It retains the field name from the original
schema. The root has one child, the outer optional group at schema
ordinal 1. The outer group contains the repeated `list` group at
ordinal 2, whose only child is the optional INT32 `element` at ordinal
3 and physical column ordinal 0. The raw Compact SchemaElement field
10 must contain exactly the LIST union arm and its empty ListType
struct. If field 6 is present, its converted code must also be LIST.
The root, repeated group and element must lack both annotation fields.
Files using only the legacy converted annotation are outside this profile.
The checked footer supplies the global row total and the order of its
row groups.
[Pinned LIST layout](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/LogicalTypes.md#lists) · [Pinned Compact fields](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/src/main/thrift/parquet.thrift)

`Checked.readGroup` selects the original zero-based row group and its
sole local chunk, verifies the full path and INT32 type, and requires
codec 0 and one complete CRC-free PLAIN V1 frame filling the declared
chunk. It matches the footer `ColumnMetaData.num_values` to the
V1 page header's level-slot count, then gives the original body to
`ListPage.decodeV1` with the group's declared row count. These two
counts differ when a row contains multiple elements. The checked frame
witness and exact decoder byte accounting include the two original
length-prefixed level streams and the ordered signed INT32 payload.
Source, footer, schema traversal, frame headers, page bodies, level
slots and rows have the existing explicit caps. Auxiliary column and
offset index spans can be present and are checked by the footer
validator. Their contents and bloom filters play no role in decoding.
External columns, dictionary or index pages, V2, compression, additional
columns, other LIST layouts, and cross-page continuation are outside the
admitted reader.
[Page rules and proof](parquet-list-v1.md) · [File contract](../../Silmaril/Formats/Parquet/ListFile/Thms.lean)

`ListFile.openSource` supplies an abstract Arrow batch event source
with one `nullableListOfNullableInt32` column. A present value has type
`List (Option Int32)`, and a nullable row cell wraps it in `Option`.
This distinguishes `none`, `some []`, `some [none]` and a list with
present elements. `readAll` emits one ordered batch per successful
group. An open error precedes the schema. A group error terminates with
the original typed cause and group ordinal, retaining all preceding
batches. The source uses the repository's abstract Arrow Events model.
Arrow IPC LIST serialization and scanner routing are separate.

`openFile_wire` binds the raw LIST tag and ordered schema items to the
same checked snapshot. `readGroup_wire` identifies its exact original
chunk, frame, payload, page slot count and ordered list rows.
`batch_slots`, `readAll_success` and `readAll_first_error` describe the
event values, batch order and retention of the prefix.

## Producer fixtures

PyArrow 26.0.1 writes and rereads two native files containing two
groups each, one uncompressed and one Snappy. Thrift 0.25.0 reads
the original annotation, full path, totals and frame boundaries
directly. The oracle independently unpacks the uncompressed levels
and signed words (including both INT32 endpoints). The Lean examples
read the uncompressed file and refuse Snappy with its codec ID. The
oracle checks same-length mutations for a wrong logical arm or
converted code, a wrong chunk path, a mismatched late slot count, and
a leading continuation in the second group. The last two preserve the
first complete batch and report the original typed cause.
[Fixture pins and mutation observations](../../scripts/parquet-list-file/observations.txt) · [Producer versions and hashes](parquet-column-index.md#pinned-independent-fixture)

```sh
set -o pipefail
replay=$(mktemp -d)
python3 scripts/parquet-list-file/Oracle.py "$replay" |
  diff -u scripts/parquet-list-file/observations.txt -
for name in nullable-int32-v1 nullable-int32-v1-snappy; do
  cmp "data/parquet-list-file/$name.parquet" "$replay/$name.parquet"
done
lake build --wfail +Silmaril.Formats.Parquet.ListFile.Examples
make check CHECK_TARGETS=+Silmaril.Formats.Parquet.ListFile.Examples
```
