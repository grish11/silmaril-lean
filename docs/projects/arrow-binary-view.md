# Arrow BinaryView and Utf8View slots

The little-endian slot reader takes the view buffer, the ordered variadic data
buffers, a physical slot index, and a per-value byte limit. The caller
identifies non-null slots. It handles the Arrow Columnar 1.5 view layout
introduced in 1.4. Array validity, IPC type dispatch and variadic buffer
count metadata are separate interfaces.
[Columnar layout, Arrow 26.0.1](https://github.com/apache/arrow/blob/9e5d6978e9acf372cc989aaaf94e863fe8582c90/docs/source/format/Columnar.rst#variable-size-binary-view-layout)

`BinaryView.readBinary` checks the whole 16-byte slot and its signed length
before reading the payload. Values of at most 12 bytes are inline and their
padding must be zero. Longer values have a nonnegative buffer index and
offset, a bounded range inside the selected buffer, and a four-byte prefix
that must agree with the payload. References can overlap. The limit is
checked before slicing or UTF-8 decoding. `BinaryView.readUtf8` reads the
same payload and requires successful UTF-8 decoding.
[Definitions](../../Silmaril/Formats/Arrow/BinaryView/Defs.lean)

`readBinary_iff` characterizes the exact inline or referenced window.
`readBinary_extent` gives its well-formedness and exact bounded length.
`readUtf8_iff` adds the UTF-8 observation to the checked wire relation.
[Laws](../../Silmaril/Formats/Arrow/BinaryView/Thms.lean)

The fixture uses PyArrow 26.0.1 to concatenate views from two input arrays.
PyArrow's BinaryView and Utf8View buffers agree byte for byte. The compiled
Lean examples check the seven valid values, including an empty value, both
sides of the inline boundary and both data buffers. Additional guards cover
overlap, short carriers, malformed signed words, range and prefix errors,
and invalid UTF-8. The pinned Linux x86-64 PyArrow wheel has SHA-256
`7ae48ab53610b85e004b03bccff593fbdf22186d0ab48ed42c90797915dac814`.
[Generator and buffer hashes](../../scripts/arrow-binary-view/fixtures.py) ·
[Lean examples](../../Silmaril/Formats/Arrow/BinaryView/Examples.lean)

## Nullable columns

The column reader takes a field node, the field's nullability, and the
physical bitmap, views and variadic data buffers. It checks the row and
buffer counts, their aggregate extent and cached lengths, bitmap coverage,
and the full logical extent of the view slots before reading values.
Trailing descriptor padding is allowed. An omitted validity buffer
denotes an all-valid column. Observed nulls must match the field node.

Each valid slot uses the checked BinaryView reader. The contents of a null
view slot do not affect the result. In addition to the per-value limit, the
column bounds the sum of observed value bytes before UTF-8 materialization.
Repeated and overlapping references each contribute their observed length.
The column interface starts at already extracted buffers, including the order
of the variadic data buffers.

`Column.checkBuffers_iff` checks range and buffer admission.
`Column.readBinary_iff` characterizes the ordered slot observation.
`Column.readBinary_bounds` and `Column.readUtf8_counts` give the declared
length and null count. `Column.readUtf8_iff` binds the text results to the
same ordered byte observations.

The same pinned PyArrow sample now includes the validity byte alongside the
views and data buffers. Lean checks all eight slots, including the null.
Other examples cover omitted validity, an empty column, a null slot with
an invalid view word, bad count and extent declarations, and the aggregate
cost of overlapping references.
[Column reader](../../Silmaril/Formats/Arrow/BinaryView/Column/Defs.lean) ·
[Column laws](../../Silmaril/Formats/Arrow/BinaryView/Column/Thms.lean) ·
[Column checks](../../Silmaril/Formats/Arrow/BinaryView/Column/Examples.lean)

## One-field V5 RecordBatch

`BinaryView.Batch.readBinary` and `BinaryView.Batch.readUtf8` take the
V5 RecordBatch metadata slice and its immutable body. The caller selects
the little-endian view profile and supplies the field's nullability.
The metadata reader checks exactly one node and a singleton
`variadicBufferCounts` vector. A count of zero must be encoded as
`[0]`. The reader rejects negative counts, checks the configured cap, and
requires exactly `2 + count` buffer descriptors before enumerating them.
The first two descriptors are validity and views, followed by the ordered
variadic data descriptors.

The binder checks the declared body length and node counts and validates
the aligned, ordered descriptor extents against the actual body before
slicing it. It passes the extracted buffers to the column reader.
`BatchMetadata.count_verified` certifies the checked count word and
descriptor cardinality. `Batch.frame_buffer_exact` and
`Batch.frame_data_at` give exact windows in descriptor order.
`Batch.readBinary_iff`, `Batch.readUtf8_iff`, and `Batch.readUtf8_counts`
characterize the decoded observation and declared counts.
[Batch laws](../../Silmaril/Formats/Arrow/BinaryView/Batch/Thms.lean)

The standalone entry point leaves the primitive message AST and admission
in place. The examples check the original Int32 admission and the legacy
rejection of variadic counts. This profile starts at RecordBatch metadata
and a body slice. The schema-bound interface below adds field dispatch.
[Pinned Message.fbs](https://github.com/apache/arrow/blob/9e5d6978e9acf372cc989aaaf94e863fe8582c90/format/Message.fbs)

Pinned PyArrow 26.0.1 emits the mixed Utf8View case with two data buffers,
a BinaryView case with a byte outside UTF-8, and a zero-row BinaryView
with a genuine `[0]` count. The all-inline Utf8View example has a count
of one and a zero-length data buffer. Lean reads all four and rejects
missing, empty, signed-negative, over-budget and mismatched count vectors,
as well as invalid descriptor ranges, body declarations and slots.

## Schema-bound one-field reader

`BinaryView.Schema.readBatch` takes three caller-paired slices: V5 Schema
metadata, V5 RecordBatch metadata and its body. It checks for a bodyless
little-endian Schema with one field. The field name is decoded as UTF-8,
and the Schema supplies the nullability and physical kind. Tags 23 and 24
select BinaryView and Utf8View, respectively, and each requires its empty
type table. Shared metadata checks reject dictionaries, children, schema
features and custom metadata. The result retains the declared field and
one ordered nullable column, with bytes or strings according to its kind.
[Schema IDL, Arrow 26.0.1](https://github.com/apache/arrow/blob/9e5d6978e9acf372cc989aaaf94e863fe8582c90/format/Schema.fbs)

`Schema.readBatch_binds` characterizes how success retains the checked
field and uses it to read the batch. `Schema.readBinary_iff` and
`Schema.readUtf8_iff` compose that result with the checked wire relation
for ordered bytes and strings. The RecordBatch does not encode a field
name or kind, so a physically compatible batch can satisfy the supplied
Schema even if it comes from another source. Framing and stream or file
assembly are outside this interface. The primitive and normalized
Schema readers still reject view tags.
[Reader](../../Silmaril/Formats/Arrow/BinaryView/Schema/Defs.lean) ·
[Laws](../../Silmaril/Formats/Arrow/BinaryView/Schema/Thms.lean)

The pinned PyArrow wheel above emits both kinds. Lean checks the nullable
BinaryView and Utf8View columns, a nonnullable Utf8View with a Unicode
field name, and a zero-row BinaryView. Rejections include an Int32 field,
a view tag with an Int32 payload, big-endian metadata, a malformed name,
wrong field counts, nulls under a nonnullable declaration and a binary
value outside UTF-8 under a Utf8View declaration.
[Fixture generator and hashes](../../scripts/arrow-binary-view/schema_fixtures.py) ·
[Lean examples](../../Silmaril/Formats/Arrow/BinaryView/Schema/Examples.lean)

```sh
lake build --wfail +Silmaril.Formats.Arrow.BinaryView.Thms +Silmaril.Formats.Arrow.BinaryView.Examples \
  +Silmaril.Formats.Arrow.BinaryView.Column.Thms +Silmaril.Formats.Arrow.BinaryView.Column.Examples \
  +Silmaril.Formats.Arrow.BinaryView.Batch.Thms +Silmaril.Formats.Arrow.BinaryView.Batch.Examples \
  +Silmaril.Formats.Arrow.BinaryView.Schema.Thms +Silmaril.Formats.Arrow.BinaryView.Schema.Examples
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/arrow-binary-view/Axioms.lean
python3 -I scripts/arrow-binary-view/fixtures.py --regenerate
python3 -I scripts/arrow-binary-view/batch_fixtures.py
python3 -I scripts/arrow-binary-view/schema_fixtures.py
```
