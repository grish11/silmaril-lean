# Arrow IPC V5 stream reader and writer

`Silmaril.Formats.Arrow.readStream` reads an in-memory
`KBytes` stream into an ordered schema and body-backed record batches. The
reader can then validate the physical buffers and materialize ordered nullable
rows with `readRows`. The profile uses Arrow Columnar 1.5 and IPC metadata V5
from Arrow 26.0.1
(`9e5d6978e9acf372cc989aaaf94e863fe8582c90`) and the FlatBuffers wire rules
at `03fffb25e2d777462b719cb4964249c30b19d58f`.
[Coverage matrix](arrow-parquet-coverage.md) ·
[Arrow Columnar and IPC](https://github.com/apache/arrow/blob/9e5d6978e9acf372cc989aaaf94e863fe8582c90/docs/source/format/Columnar.rst) ·
[Arrow IDLs](https://github.com/apache/arrow/tree/9e5d6978e9acf372cc989aaaf94e863fe8582c90/format) ·
[FlatBuffers internals](https://github.com/google/flatbuffers/blob/03fffb25e2d777462b719cb4964249c30b19d58f/docs/source/internals.md)

## Reader contract

- `readEnvelope` checks the modern continuation word, signed 32-bit length
  domain, eight-byte alignment, and availability of the padded metadata.
  `readBody` checks alignment and slices exactly the declared body.
  [Framing](../../Silmaril/Formats/Arrow/Framing/Defs.lean)
- `readMessage` resolves the root, signed vtable displacements (including
  shared vtables on either side), field offsets and defaults, forward
  references, fixed-stride vectors and terminated UTF-8 names. It admits
  little-endian schemas of flat signed Int32 and Utf8 fields, preserving names
  and nullability. An omitted name becomes the empty string. Batch metadata
  preserves the row count and ordered field nodes and buffer descriptors.
  [Metadata](../../Silmaril/Formats/Arrow/Metadata/Defs.lean)
- `validateBatch` checks the exact descriptor counts for the schema, field
  node lengths and null counts, and aligned, ordered, nonoverlapping buffer
  ranges within the declared body. It permits gaps and zero-length buffers.
  `BatchFrame` carries this validation as a proof field.
  [Layout](../../Silmaril/Formats/Arrow/Layout/Defs.lean)
- `readStream` requires one bodyless schema first, zero or more record batches
  and explicit EOS at the end of the input. EOF-only termination and trailing
  bytes are outside this profile. The result retains batch boundaries and raw
  body bytes. [Stream](../../Silmaril/Formats/Arrow/Stream/Defs.lean)
- `decodeBatch` checks the per-batch limits on a frame and reads two buffers
  per Int32 field and three per Utf8 field. An omitted validity bitmap denotes
  all-valid slots. A materialized bitmap uses the low bit first and covers
  every slot. The observed null count must match the field node. Padding
  beyond the required bitmap and values extents has no observable value.
  Signed Int32 values use four little-endian bytes per slot.
- Utf8 uses `rowCount + 1` little-endian signed 32-bit offsets. All offsets
  must be nonnegative, monotonic and bounded by the data buffer. The reader
  accepts a nonzero first offset and checks the sole offset of an empty
  column. It decodes each valid span with the strict UTF-8 decoder. A null
  slot may span arbitrary bytes and still requires valid offsets.
- `readRows` checks aggregate row and cell limits before materialization.
  Its result retains the schema, row and field order, and batch boundaries.
  Rows in an empty schema still count against the budget.
  [Body reader](../../Silmaril/Formats/Arrow/Body/Defs.lean)

The error type distinguishes malformed bytes or stream structure, unsupported
wire features, and configured resource limits. Unsupported features include
legacy framing, other metadata versions, big-endian schemas, other schema
types or message tags, dictionaries, nonempty children or features, custom
metadata, compression and variadic buffers. Unrecognized vtable slots of
supported tables also give `unsupported`. Once an unsupported feature is
identified, its contents are outside the reader's validation. The budgets are
metadata and body bytes per message, fields per schema (also bounding node and
buffer vector counts), rows per batch, and batches per stream.
[Errors and limits](../../Silmaril/Formats/Arrow/Framing/Defs.lean)

## Laws and evidence

- `readEnvelope_iff` characterizes successful modern framing over a list of
  octets. `metadata_exact`, `readBody_iff` and `body_exact` give exact
  windows, and `readEnvelope_rechunk` preserves successful envelope
  observations for well-formed byte trees with equal octets.
  [Framing theorems](../../Silmaril/Formats/Arrow/Framing/Thms.lean)
- `validateBatch_iff` characterizes validation against the descriptor
  relation. `BuffersFit.mem_fits` and `BatchFrame.buffer_exact` give aligned,
  bounded descriptors and exact byte windows.
  [Layout theorems](../../Silmaril/Formats/Arrow/Layout/Thms.lean)
- `Body.validAt_iff` states bitmap interpretation over octets and
  `Body.offsetAt_iff` relates offsets to checked little-endian words.
  `Body.readCell_iff`, `Body.readColumn_iff` and `decodeBatch_iff` characterize
  accepted observations slot by slot, including null counts, offset bounds
  and strict UTF-8 values. `BatchWire.shape` gives exact row count and width.
  [Body theorems](../../Silmaril/Formats/Arrow/Body/Thms.lean)
- The native suite reads the pinned PyArrow-produced fixture, checks schema,
  descriptors, exact body bytes and ordered nullable rows across all 1,129
  two-way splits, rejects all 1,128 proper prefixes, and exercises malformed,
  unsupported and limit cases. The fixture contains mixed validity, an empty batch, an all-null
  batch, and a batch with omitted validity buffers. The fixture's ordered rows
  are checked independently by PyArrow during regeneration. The body tests
  also cover short bitmaps and values, null-count mismatches, invalid
  offsets and UTF-8, omitted validity, empty and zero-column batches, and
  configured aggregate limits.
  [Fixture manifest](../../tests/formats/arrow-ipc/fixture.json) ·
  [Native tests](../../tests/formats/arrow-ipc/MetadataTests.lean) ·
  [Kernel vectors and axiom audit](../../tests/formats/arrow-ipc/Axioms.lean)

Run from the repository root.

```sh
lake build --wfail +Silmaril.Formats.Arrow.Framing.Thms +Silmaril.Formats.Arrow.Layout.Thms +Silmaril.Formats.Arrow.Body.Thms arrow_ipc_metadata_tests
make check CHECK_TARGETS='+Silmaril.Formats.Arrow.Framing.Thms +Silmaril.Formats.Arrow.Layout.Thms +Silmaril.Formats.Arrow.Body.Thms arrow_ipc_metadata_tests'
```

To reproduce the fixture on Linux x86-64 with CPython 3.14, install the
PyArrow and NumPy wheels listed in the [fixture requirements](../../tests/formats/arrow-ipc/requirements.txt)
using `python3 -m pip install --require-hashes -r tests/formats/arrow-ipc/requirements.txt`.
Then run `python3 -I tests/formats/arrow-ipc/fixture.py --regenerate`. The
generator checks both PyArrow versions, the PyArrow readback and the digest
before replacing the fixture.
[PyArrow 26.0.1 distribution](https://pypi.org/project/pyarrow/26.0.1/#files)

## Physical batch writer

`Writer.emitBatch` accepts typed nullable columns, field names and
nullability, and an explicit row count. It emits the aligned physical body
and the batch metadata AST as a checked `BatchFrame`. The writer emits
LSB-first validity, four-byte little-endian Int32 values, and nonnegative
signed-32 UTF-8 offsets beginning at zero. Null slots use zero or empty
payloads. Every buffer starts at an eight-byte boundary and its descriptor
excludes padding. Empty UTF-8 columns have one zero offset. The explicit
count preserves rows in a zero-column batch.
[Writer definitions](../../Silmaril/Formats/Arrow/Writer/Defs.lean)

`Writer.checkInput_iff` specifies admission by schema shape, nullability,
signed offset and batch size ranges, and budgets. `Writer.packBuffers_exact` identifies the
exact descriptor windows. `Writer.emitBatch_of_admitted` proves every
admitted input emits a frame with the original count and an aligned body,
and that the checked reader returns the original ordered nullable
observation. `Writer.emitBatch_roundtrip` states the same properties for
every successful emission. The proof uses per-column and packing laws.
[Writer theorems](../../Silmaril/Formats/Arrow/Writer/Thms.lean)

The native suite checks mixed, empty, and nonempty zero-column batches and
budget and shape rejection. To verify the emitted physical buffers with the
pinned PyArrow environment described above, run the following.

```sh
lake build --wfail +Silmaril.Formats.Arrow.Writer.Thms arrow_ipc_metadata_tests
.lake/build/bin/arrow_ipc_metadata_tests --write-body-fixtures /tmp/arrow-bodies
python3 -I tests/formats/arrow-ipc/read_writer_fixtures.py /tmp/arrow-bodies
```

The fixture driver writes raw body bytes and a JSON representation of the
metadata AST. PyArrow reads those exact byte windows as arrays and checks
ordered rows, null counts, and full array validity.
[Independent buffer checks](../../tests/formats/arrow-ipc/read_writer_fixtures.py)

## FlatBuffers and stream writer

`MetadataWriter.serialize` emits the Arrow V5 Message, Schema, Field, Int,
Utf8, and RecordBatch tables. It uses forward relative uoffsets and
non-deduplicated vtables. It checks signed wire ranges and the configured
metadata, row and field limits before emitting bytes. Table positions and
inline struct alignment are relative to the metadata slice.
`MetadataWriter.emit` checks exact AST recovery using the existing reader on
that slice. The `serialize_extent` and `wireSize_aligned` laws hold independently of
that check.
[Metadata definitions](../../Silmaril/Formats/Arrow/MetadataWriter/Defs.lean)
[Metadata theorems](../../Silmaril/Formats/Arrow/MetadataWriter/Thms.lean)

`StreamWriter.emit` writes a bodyless schema, a list of batches in order,
and the modern EOS marker. It requires matching schemas and checks the
batch count and aggregate observation budgets. `StreamWriter.emitFrame_exact`
proves that the framing, metadata and body readers recover the original
message and exact body octets from a successful frame write.
`StreamWriter.read_eos` proves recognition of the emitted EOS.
[Stream definitions](../../Silmaril/Formats/Arrow/StreamWriter/Defs.lean)
[Framing theorems](../../Silmaril/Formats/Arrow/StreamWriter/Thms.lean)

With the hash-pinned PyArrow environment above, the following commands
exercise the native reader and write complete IPC streams for independent
readback. PyArrow's IPC reader checks the field order, types, nullability,
ordered nullable values and explicit batch row counts. The cases include
mixed and empty batches in one stream, a schema with zero batches, and
a zero-column schema with three-row and zero-row batches.

```sh
lake build --wfail +Silmaril.Formats.Arrow.StreamWriter.Thms arrow_ipc_metadata_tests
.lake/build/bin/arrow_ipc_metadata_tests --write-stream-fixtures /tmp/arrow-streams
python3 -I tests/formats/arrow-ipc/read_writer_fixtures.py --streams /tmp/arrow-streams
```

[Independent IPC checks](../../tests/formats/arrow-ipc/read_writer_fixtures.py)

## Whole-stream round trip

`StreamWriter.emit_roundtrip` proves that a successful `emit` can be read
by `readStream` and `readRows` under the same `ObservationLimits`.
It preserves the declared schema, including nullability, the order and
boundaries of batches, and all ordered nullable rows. The count in each
record's metadata and the length of its observed row list both equal the
declared input count. Thus an empty batch remains in the list, and three
rows at zero columns read as three empty rows.
`StreamWriter.emit_readRows` is the direct ordered observation law.
[Whole-stream theorem](../../Silmaril/Formats/Arrow/StreamWriter/Thms.lean)

The writer checks schema equality, message representability, the per-message
and batch limits, and aggregate row and cell limits. The proof derives the
reader's allocation checks from these executable guards and the exact
recovered metadata. It uses the physical batch round trip after transporting
buffer reads through the containing stream.
The law applies to the emitted byte carrier and a successful write at the
same limits. The native suite also rereads the emitted octets at the exact
field, row, batch and aggregate limits.

## Remaining scope

The profile covers flat nullable and required Int32 and UTF-8. Nested fields,
dictionaries, and compression are outside it. The law concerns the forward
write/read direction on successful writes. Raw metadata admission
completeness, arbitrary rechunking of whole streams, and incremental I/O
remain open.
