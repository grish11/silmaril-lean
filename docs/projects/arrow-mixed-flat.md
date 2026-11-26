# Mixed-flat Arrow IPC V5 RecordBatch

`Arrow.MixedFlat.readBatch` consumes three caller-paired slices for a
bodyless little-endian Schema, RecordBatch metadata, and body. It admits
nullable or required Int32, Utf8, BinaryView and Utf8View fields and
returns the explicit batch row count and ordered field/column
observations. Compression, dictionaries, nested fields and
temporal types are outside this profile.
[Pinned Arrow 26.0.1 Schema IDL](https://github.com/apache/arrow/blob/9e5d6978e9acf372cc989aaaf94e863fe8582c90/format/Schema.fbs) ·
[RecordBatch IDL](https://github.com/apache/arrow/blob/9e5d6978e9acf372cc989aaaf94e863fe8582c90/format/Message.fbs)

Every field consumes one node. Int32 takes two descriptors and Utf8 takes
three. A view takes two descriptors plus its own signed nonnegative count
of additional descriptors. Only views consume count entries, in Schema
order, including entries equal to zero. The metadata reader checks the
node and count cardinalities and per-view and total count limits. It
checks the resulting descriptor cardinality before reading descriptors.

The binder checks the common row count and nullability against every
node, and checks the entire ordered descriptor list against the
immutable body before slicing. Column decoding uses the existing
primitive bitmap, offset and value readers and the existing nullable
view slot readers. The batch uses configured row and cell budgets, and
views also use their per-column buffer and observed-value byte budgets.
Plan and column errors carry zero-based Schema field indices. Negative
or over-limit count diagnostics instead carry the zero-based position in
the count vector, which contains only view entries.
[Reader and planner](../../Silmaril/Formats/Arrow/MixedFlat/Defs.lean)

`Assignment.exact` reconstructs the input fields, nodes, counts and
descriptors in order from the plan. `Group.shape` ties each field to its
node length, count presence and descriptor width. `Plan.ordered_disjoint`
proves ordered non-overlap across arbitrary descriptor positions, and
`Plan.buffer_exact` identifies the exact body bytes for each assigned
descriptor. `Plan.readGroups_fields` preserves the declared field order
on successful column decoding. `readBatch_shape` relates the returned
Schema order and row count to the checked metadata.
[Laws](../../Silmaril/Formats/Arrow/MixedFlat/Thms.lean)

The independent PyArrow 26.0.1 fixtures have two view columns, with
counts `[2, 1]`, `[1, 2]` after reordering and `[0, 0]` for a zero-row
batch. The pinned Linux x86-64 CPython 3.14 wheel has SHA-256
`7ae48ab53610b85e004b03bccff593fbdf22186d0ab48ed42c90797915dac814`.
The generated Schema, RecordBatch and body slices are checked in as Lean
bytes. Lean checks ordered values and rejects missing, excess, negative
and over-budget entries, cross-field overlap, mismatched nodes and a
same-total count swap that deprives one field of a referenced buffer.
[Generator](../../scripts/arrow-mixed-flat/fixtures.py) ·
[Lean fixture checks](../../Silmaril/Formats/Arrow/MixedFlat/Examples.lean)

## Modern V5 streams

`Arrow.MixedFlat.Stream.read` admits the first Schema once and checks each
RecordBatch with the shared continuation-envelope and body readers. Each
batch observation retains its envelope offset, padded metadata size, and
declared body length. These determine the metadata and body slices on
the original carrier and the next envelope offset. The reader keeps each
zero-row batch and requires explicit EOS at the carrier end.

After the Schema, typed errors carry the zero-based batch index. The
stream checks its running row and cell budgets before decoding each new
batch. Column failures retain their field index within that batch.
[Reader](../../Silmaril/Formats/Arrow/MixedFlat/Stream/Defs.lean)

`Stream.read_iff` characterizes the ordered frames through exact EOS.
`Stream.RecordWire.ranges` gives the exact body and metadata windows
for admitted envelopes, and `Stream.read_batch_results` proves that
standalone batch decoding over those ranges recovers the ordered stream
observations.
[Laws](../../Silmaril/Formats/Arrow/MixedFlat/Stream/Thms.lean)

The same pinned PyArrow wheel emits a stream with batch sizes
`[4, 0, 2]` and a schema-only stream. It reads the first two batches of a
derived fixture and rejects the truncation in the third body. Lean
checks the exact ranges and nullable values and distinguishes late body
truncation, envelope truncation, a corrupt view slot, budget exhaustion,
missing EOS and trailing bytes.
[Stream fixture generator](../../scripts/arrow-mixed-flat/stream_fixtures.py) ·
[Lean stream guards](../../Silmaril/Formats/Arrow/MixedFlat/Stream/Examples.lean)

```sh
lake build --wfail +Silmaril.Formats.Arrow.MixedFlat.Thms +Silmaril.Formats.Arrow.MixedFlat.Examples \
  +Silmaril.Formats.Arrow.MixedFlat.Stream.Thms +Silmaril.Formats.Arrow.MixedFlat.Stream.Examples
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/arrow-mixed-flat/Axioms.lean
python3 -I scripts/arrow-mixed-flat/fixtures.py
python3 -I scripts/arrow-mixed-flat/stream_fixtures.py
```

## Indexed V5 files

`Arrow.MixedFlat.File.readIndex` checks both `ARROW1` words, padding and the
footer range on one immutable source. It uses the shared V5 footer parser
and requires exact agreement with the embedded Schema. Aligned record
blocks occupy contiguous ranges in footer order, followed by the modern
EOS immediately before the footer. The checker validates the entire index
before any RecordBatch is decoded. [Pinned File.fbs](https://github.com/apache/arrow/blob/9e5d6978e9acf372cc989aaaf94e863fe8582c90/format/File.fbs)

`Index.readAt` validates the selected continuation prefix and Message
lengths against the footer. It uses the same per-batch row, cell and view
budgets as standalone decoding. An absent entry gives `none`, while a
bad record carries its zero-based footer index. Each call decodes only
the selected record, so errors in later records are reported when those
records are read. The API uses a finite in-memory source and a bounded
footer list. Stream-wide cumulative budgets apply to the stream API.
[Definitions](../../Silmaril/Formats/Arrow/MixedFlat/File/Defs.lean)

`readIndex_exact` recovers the checked footer, Schema and EOS. `Index.block_range`
and `Index.block_order` prove alignment, extent and nonoverlap. `Index.readAt_exact`
identifies the selected entry, exact source octets and the same standalone
`MixedFlat.readBatch` result. `Index.readAt_sequential` equates lookups with
the corresponding observations of a successful ordered traversal, including
empty batches and absent entries. [Theorem header](../../Silmaril/Formats/Arrow/MixedFlat/File/Thms.lean)

The pinned PyArrow producer emits and independently opens files with row
counts `[4, 0, 2]` and `[]`. Their SHA-256 digests are
`efec769981c07a0c25fbaff56dc7af79ee9facfbda14a9099a52b89b7287516a` and
`ca999237b082b55fae3bc82d0ed7339bd66898ceaf92b90a016ee11fa404c8a8`.
Lean compares indexed values with the independently pinned stream and
checks malformed footer ranges, schema disagreement, missing EOS and
indexed length mismatches. [File fixture producer](../../scripts/arrow-mixed-flat/file_fixtures.py) · [Lean file guards](../../Silmaril/Formats/Arrow/MixedFlat/File/Examples.lean)

```sh
lake build --wfail +Silmaril.Formats.Arrow.MixedFlat.File.Examples +Silmaril.Formats.Arrow.MixedFlat.File.Axioms
python3 -I scripts/arrow-mixed-flat/file_fixtures.py
```

## Checked Int32 and BinaryView RecordBatch writer

`MixedFlat.Writer.emit` takes one Int32 column, one BinaryView column, an
explicit common row count, and a choice of field order. Names and
nullability come from the input. Each field may be nullable or required.
The result contains V5 RecordBatch metadata bytes, their exact metadata
AST, and the aligned body. A reader supplies the field declarations in
the same order because a RecordBatch Message carries no Schema.

The writer reuses the two physical encoders and packs their buffers in
field order. It writes an explicit signed 64-bit count for the view,
zero for inline-only and empty columns and one for a column with external
values. It checks lengths against the common row count and enforces the
configured field, row, cell, view and byte limits. The padded body
budget is checked before packing. It certifies the output by parsing the
RecordBatch metadata, comparing the exact AST, and running
`MixedFlat.readParsed` and comparing the ordered column observations.
This entails a full read and value comparison. All byte limits apply to
this batch.
[Definitions](../../Silmaril/Formats/Arrow/MixedFlat/Writer/Defs.lean)

`Wire.metadata_extent` gives the exact serialized metadata size.
`emit_layout` fixes the row count, field nodes, view count, aligned body
and exact packed descriptor windows. `emit_assignment` gives the
reader's exhaustive schema-order plan. `emit_partition` identifies the
two descriptor groups and the view's count in either field order.
`emit_readback` recovers the exact metadata, row count and ordered
nullable values. BinaryView equality compares octets per present cell.
[Laws](../../Silmaril/Formats/Arrow/MixedFlat/Writer/Thms.lean)

Pinned PyArrow 26.0.1 reads four standalone Lean-emitted RecordBatch
Messages with independently supplied field declarations. It checks the
row and null counts, descriptor order and extents, signed variadic
count vector, and ordered values. Cases cover both field orders, signed
Int32 extremes, nullable and required columns, zero rows, and the 12/13
byte threshold. Lean guards reject inconsistent row counts, nulls in
required fields, and exhausted body, metadata and data-buffer limits.
The fixture driver supplies one modern continuation prefix for PyArrow.
The library API emits the metadata and body of a single RecordBatch.
[Oracle](../../scripts/arrow-mixed-flat/writer_fixtures.py) ·
[Lean examples](../../Silmaril/Formats/Arrow/MixedFlat/Writer/Examples.lean)

```sh
make check CHECK_TARGETS='+Silmaril.Formats.Arrow.MixedFlat.Writer.Examples +Silmaril.Formats.Arrow.MixedFlat.Writer.Axioms'
python3 -I scripts/arrow-mixed-flat/writer_fixtures.py --out /tmp/arrow-mixed-flat-record-writer
```

## Checked Int32 and BinaryView stream writer

`MixedFlat.StreamWriter.emit` takes one `Schema` and a list of
`BatchInput` values. The schema declares the Int32 and BinaryView names,
nullability, and field order. Each batch supplies its explicit row count,
ordered nullable Int32 slots and ordered nullable `KBytes` slots. A
schema-only stream retains both declarations. A zero-row batch still emits
one RecordBatch and consumes one unit of the batch-count limit.

The writer emits one little-endian V5 Schema, then reuses the standalone
writer for every RecordBatch. It uses modern continuation framing and
terminates with explicit EOS. Running row and cell budgets are checked
before record encoding. Their failure names the zero-based batch index.
Standalone writer failures keep both the batch index and any field
index. IPC body and metadata byte caps bound individual frames, while the
column byte caps apply in each batch. The whole stream has a batch-count
cap and cumulative row and cell caps.

Successful emission reads back the complete stream with
`MixedFlat.Stream.read` and compares the exact field declarations and
ordered values. This adds a stream decoding and comparison pass to the
standalone writer's per-batch checks.
[Definitions](../../Silmaril/Formats/Arrow/MixedFlat/StreamWriter/Defs.lean)

`Wire.schema_extent` gives the precise Schema metadata extent.
`emit_readback` proves exact schema ordering and equality of nullable
observations, with BinaryView cells observed by their octets.
`emit_batch_rows` preserves the outer batch count and every row count.
`emit_wire` ties those observations to the checked source ranges and EOS
at the end of the carrier.
[Laws](../../Silmaril/Formats/Arrow/MixedFlat/StreamWriter/Thms.lean)

Pinned PyArrow 26.0.1 reads five Lean-written streams. The cases include
both orders with row counts `[4, 0, 2]`, required fields, a schema-only
stream and the same schema with one empty batch. The oracle checks both
names and nullability, every value, every modern prefix and aligned body
extent, and final EOS. Lean guards exercise indexed record and budget
errors, and the existing PyArrow-generated mixed stream still serves as
an independent inbound control.
[PyArrow oracle](../../scripts/arrow-mixed-flat/stream_writer_fixtures.py) ·
[Lean examples](../../Silmaril/Formats/Arrow/MixedFlat/StreamWriter/Examples.lean)

```sh
make check CHECK_TARGETS='+Silmaril.Formats.Arrow.MixedFlat.StreamWriter.Examples +Silmaril.Formats.Arrow.MixedFlat.StreamWriter.Axioms'
python3 -I scripts/arrow-mixed-flat/stream_writer_fixtures.py --out /tmp/arrow-mixed-flat-stream-writer
```
