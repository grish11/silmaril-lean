# Mixed-flat Arrow IPC V5 RecordBatch

`Arrow.MixedFlat.readBatch` consumes three caller-paired slices for a
bodyless little-endian Schema, RecordBatch metadata, and body. It admits
nullable or required Int32, Utf8, BinaryView and Utf8View fields and
returns the explicit batch row count and ordered field/column
observations. File IPC, compression, dictionaries, nested fields and
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
