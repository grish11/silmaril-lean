# Arrow IPC V5 files

The file reader covers the same flat little-endian nullable and required
Int32 and UTF-8 fields as the stream profile. It reads a finite immutable
`KBytes` source and provides indexed batches and ordered row observations.
The format pins are Arrow Columnar 1.5 and IPC metadata V5 at
`9e5d6978e9acf372cc989aaaf94e863fe8582c90`, and FlatBuffers at
`03fffb25e2d777462b719cb4964249c30b19d58f`.
[Coverage matrix](arrow-parquet-coverage.md) · [Stream profile](arrow-ipc-stream.md) ·
[File format](https://github.com/apache/arrow/blob/9e5d6978e9acf372cc989aaaf94e863fe8582c90/docs/source/format/Columnar.rst#ipc-file-format) ·
[File.fbs](https://github.com/apache/arrow/blob/9e5d6978e9acf372cc989aaaf94e863fe8582c90/format/File.fbs) ·
[FlatBuffers internals](https://github.com/google/flatbuffers/blob/03fffb25e2d777462b719cb4964249c30b19d58f/docs/source/internals.md)

## Footer and index

`FileFooter` retains the schema and ordered `FileBlock` entries after checking
V5, absent or empty dictionary and custom metadata vectors, and the supported
schema profile. Each inline block is 24 bytes with a signed 64-bit absolute
offset, a signed 32-bit metadata length including the continuation prefix
and metadata padding, and a signed 64-bit body length. The decoder rejects
negative values. The shared vector decoder checks element alignment for
nonempty vectors and checks the length word and extent for every vector.
[Metadata decoder and AST](../../Silmaril/Formats/Arrow/Metadata/Defs.lean)

`readFooterSpan` checks both `ARROW1` words, zero leading padding, the
signed little-endian footer length, its alignment and its extent against
the actual source. `readIndex` checks that the embedded schema matches the
footer schema exactly. The supported profile requires contiguous blocks in
physical order followed by the eight-byte modern EOS immediately before
the footer. Each block must be aligned, start at the current cursor, and
end before the footer. This checks the full index before any indexed
metadata or bodies are sliced.
[File reader definitions](../../Silmaril/Formats/Arrow/FileReader/Defs.lean)

An indexed read checks the prefix and Message lengths against the selected
block, validates the record layout, and uses the existing body decoder.
An out-of-range index returns `none`. Indexed row reads check the selected
batch budgets. Full materialization checks aggregate rows and cells before
allocating row observations. Malformed input, unsupported features, and
configured limits use the same error classes as the stream reader.

## Laws and independent fixtures

`readFooterSpan_verified` and `FooterSpan.bytes_exact` characterize the checked
footer. `Index.block_range` and `Index.block_order` prove its range and
nonoverlap properties. `Index.readBlock_exact` proves that a successful
indexed read recovers the declared metadata and exact body octets.
`readRows_indexed` proves that materialization and indexed reads agree,
including batch order, empty batches, and out-of-range lookups.
[Theorem header](../../Silmaril/Formats/Arrow/FileReader/Thms.lean) ·
[Axiom audit](../../Silmaril/Formats/Arrow/FileReader/Axioms.lean)

The pinned PyArrow 26.0.1 producer uses `pa.ipc.new_file`. Its independent
`pa.ipc.open_file` readback checks schema, batch lengths and ordered rows.
The fixtures include mixed nulls and multiple batches, an empty batch,
a schema-only file, and positive-row zero-column data. Dictionary and Int64
files are pinned rejection cases. The native Lean target runs the SHA-256
checker against the tracked fixture inputs. It tests indexing and materialization
and mutates footer lengths, offsets, schemas and block extents.
[Fixture hashes](../../tests/formats/arrow-ipc/file-fixtures.json) ·
[Producer and wheel hash](../../tests/formats/arrow-ipc/fixture.json) ·
[Hash-pinned requirements](../../tests/formats/arrow-ipc/requirements.txt)

```sh
lake build --wfail +Silmaril.Formats.Arrow.FileReader.Axioms arrow_ipc_metadata_tests
make check CHECK_TARGETS='+Silmaril.Formats.Arrow.FileReader.Axioms arrow_ipc_metadata_tests'
python3 -I tests/formats/arrow-ipc/file_fixture.py --regenerate
```

Regeneration uses the environment installed from the hash-pinned requirements.
Dictionaries, nested types, compression, legacy
framing, and incremental file I/O remain outside the profile.

## Checked file writer

`FileWriter.emit` takes the same fields, typed batches and observation limits
as the stream writer. It uses the existing physical writer and modern frame
encoder, adds the file magic and EOS, and writes the footer and signed
little-endian trailer length. Each footer block uses the metadata and body
lengths of its emitted frame. The footer encoder reuses the relocatable
schema payload used in stream messages.
[File writer](../../Silmaril/Formats/Arrow/FileWriter/Defs.lean) ·
[Footer encoder](../../Silmaril/Formats/Arrow/FooterWriter/Defs.lean)

`FooterWriter.serialize_extent` proves the exact padded footer length within
the signed and configured bounds. `FooterWriter.emit_exact` proves checked
readback of the schema and ordered block AST. `FileWriter.packRecords_exact`
proves the blocks are contiguous, aligned and in frame order.
`FileWriter.assemble_extent` proves that assembly accounts for the declared
schema, batch count and all byte extents. `FileWriter.emit_index_exact`
proves that a checked write recovers its exact planned footer and boundaries
with `FileReader.readIndex`. The writer checks the index before returning
the bytes. `FileWriter.emit_roundtrip` proves that under the same limits,
`FileReader.readRows` returns the declared schema and one ordered nullable
observation per input batch. It also proves the indexed metadata counts
and observation lengths equal the declared counts, including empty batches
and positive-row zero-column batches.
[File writer laws](../../Silmaril/Formats/Arrow/FileWriter/Thms.lean) ·
[Footer laws](../../Silmaril/Formats/Arrow/FooterWriter/Thms.lean) ·
[Axiom audit](../../Silmaril/Formats/Arrow/FileWriter/Axioms.lean)

```sh
make check CHECK_TARGETS='+Silmaril.Formats.Arrow.FileWriter.Axioms arrow_ipc_metadata_tests'
.lake/build/bin/arrow_ipc_metadata_tests --write-file-fixtures /tmp/arrow-files
python3 -I tests/formats/arrow-ipc/read_writer_fixtures.py --files /tmp/arrow-files
```

The pinned PyArrow reader opens the complete Lean-written files and checks
schema, nullable cells and batch counts. It exercises mixed and empty
batches, a schema-only file, and a positive-row zero-column batch.
[Independent reader](../../tests/formats/arrow-ipc/read_writer_fixtures.py)

## Opt-in files with a footer-only Schema

`FileReader.FooterOnly.readIndex` provides an explicit compatibility
entry point for little-endian V5 Int32/UTF-8 files emitted without the
embedded Schema Message. It takes field declarations exclusively from
the checked footer. The pinned file specification calls for an embedded
Schema identical to the footer's copy. The strict entry point
`FileReader.readIndex` enforces that contract. Callers select the
footer-only entry point explicitly.
[File specification](https://github.com/apache/arrow/blob/9e5d6978e9acf372cc989aaaf94e863fe8582c90/docs/source/format/Columnar.rst#ipc-file-format) ·
[Definitions](../../Silmaril/Formats/Arrow/FileReader/FooterOnly/Defs.lean)

The six magic bytes and two zero padding bytes end at byte 8. All blocks
are aligned and contiguous in footer order from byte 8. The eight-byte
modern EOS starts at the end of the last block and ends at the start of
the footer. The layout admits zero inter-frame gap bytes. Schema-only
files have EOS at byte 8 and the footer at byte 16. For a nonempty index,
admission checks that the leading Message is a RecordBatch with the
indexed metadata and body extents. Selected reads check each requested
block against its original Message before taking its body, and apply
the existing row and cell budgets. An absent index returns `.ok none`.
A malformed later block can fail on selection while its neighbors remain
readable.

`readIndex_exact` relates the retained declarations and ordered blocks
to the exact bounded footer. `readIndex_firstRecord` and
`readIndex_schema_only` characterize the two admitted file starts.
`Index.block_order` proves physical order and non-overlap.
`Index.readBatchAt_exact` identifies the selected original metadata and
body byte ranges. `Index.readRowsAt_exact` connects the selected batch
to its checked row observation.
[Laws](../../Silmaril/Formats/Arrow/FileReader/FooterOnly/Thms.lean)

The locked Apache Arrow JS `21.2.0` package produces a two-batch file and
a schema-only file. The public npm archive SHA-256 is
`dd63a3a4c380eddeb00c718740414ff33c4ded015c8720798afdfcc61b5dac41`.
The producer ran with Node `26.13.1` and npm `11.20.0`.
Pinned PyArrow 26.0.1 reads the batches by index and compares the exact
ordered rows, field names and nullability. The Lean fixture module
contains the original bytes. Lean guards cover both files, independent
selected order, out-of-range indices, proper-prefix truncation, gaps,
malformed footer entries, incorrect EOS, and valid or malformed leading
Schema Messages.
[Producer and locked dependencies](../../scripts/arrow-footer-only-file) ·
[SHA-256 and independent oracle](../../scripts/arrow-footer-only-file/check.py) ·
[Lean fixture guards](../../Silmaril/Formats/Arrow/FileReader/FooterOnly/Examples.lean) ·
[PyArrow wheel pin](../../tests/formats/arrow-ipc/requirements.txt)

```sh
make check CHECK_TARGETS='+Silmaril.Formats.Arrow.FileReader.FooterOnly.Examples +Silmaril.Formats.Arrow.FileReader.FooterOnly.Axioms arrow_ipc_metadata_tests'
(cd scripts/arrow-footer-only-file && npm ci --ignore-scripts --no-audit --no-fund && node generate.cjs /tmp/arrow-footer-only-files)
python3 -I scripts/arrow-footer-only-file/check.py /tmp/arrow-footer-only-files
```
