# Arrow IPC V5 stream metadata

`Silmaril.Formats.Arrow.readStream` reads an in-memory
`KBytes` stream into an ordered schema and body-backed record batches. The
profile uses Arrow Columnar 1.5 and IPC metadata V5 from Arrow 26.0.1
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
- The native suite reads the pinned PyArrow-produced fixture, checks schema
  and ordered descriptors and bodies across all 1,129 two-way splits, rejects
  all 1,128 proper prefixes, and exercises malformed, unsupported and limit
  cases. The fixture contains mixed validity, an empty batch, an all-null
  batch, and a batch with omitted validity buffers. The fixture's ordered rows
  are checked by PyArrow during regeneration. Lean's observation ends at
  metadata and raw body bytes.
  [Fixture manifest](../../tests/formats/arrow-ipc/fixture.json) ·
  [Native tests](../../tests/formats/arrow-ipc/MetadataTests.lean) ·
  [Kernel vectors and axiom audit](../../tests/formats/arrow-ipc/Axioms.lean)

Run from the repository root.

```sh
lake build --wfail +Silmaril.Formats.Arrow.Framing.Thms +Silmaril.Formats.Arrow.Layout.Thms arrow_ipc_metadata_tests
make check CHECK_TARGETS='+Silmaril.Formats.Arrow.Framing.Thms +Silmaril.Formats.Arrow.Layout.Thms arrow_ipc_metadata_tests'
```

To reproduce the fixture on Linux x86-64 with CPython 3.14, install the
PyArrow and NumPy wheels listed in the [fixture requirements](../../tests/formats/arrow-ipc/requirements.txt)
using `python3 -m pip install --require-hashes -r tests/formats/arrow-ipc/requirements.txt`.
Then run `python3 -I tests/formats/arrow-ipc/fixture.py --regenerate`. The
generator checks both PyArrow versions, the PyArrow readback and the digest
before replacing the fixture.
[PyArrow 26.0.1 distribution](https://pypi.org/project/pyarrow/26.0.1/#files)

## Body codec handoff

The next reader interface can accept `BatchFrame fields` and return
`Except Error (BatchValues fields)`, where `BatchValues` retains the row
count and typed columns of nullable values. Consume two descriptors for
Int32 (validity and values) and three for Utf8 (validity, offsets and data).
Use the checked little-endian reads, LSB-first bitmap reads and strict UTF-8
decoder to validate the physical buffers. The body laws need to cover bitmap
size and null counts, signed offset monotonicity and bounds, UTF-8, and row
alignment. The local observation can enumerate rows in schema order and use
the explicit count even for an empty schema. A writer can then accept the
same typed batches and emit modern V5 schema and record batches plus EOS,
with a decode-after-encode law over ordered nullable rows and PyArrow
readback. The current increment leaves those body laws, row decoding,
whole-stream re-chunking proof, and writing open.
[Checked byte reads](../../Silmaril/Prelude/Bytes/Thms.lean) ·
[LSB reader](../../Silmaril/Formats/Compression/Bits/Bitstream.lean) ·
[UTF-8 laws](../../Silmaril/Formats/Utf8/Thms.lean)
