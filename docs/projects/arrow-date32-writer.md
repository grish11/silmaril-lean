# Checked native Arrow Date32 stream writer

`Arrow.DateStream.Writer.emit` writes a single named Date32 field with
explicit declared nullability and ordered batches of signed Int32 day
words. The little-endian IPC V5 Schema uses the DATE union tag and an
explicit DAY value. DAY is encoded as zero, and the Date table's vtable
marks its slot present. An omitted DateUnit would default to MILLISECOND.
[Schema.fbs at Arrow 26.0.1](https://github.com/apache/arrow/blob/9e5d6978e9acf372cc989aaaf94e863fe8582c90/format/Schema.fbs)
· [IPC stream framing](https://github.com/apache/arrow/blob/9e5d6978e9acf372cc989aaaf94e863fe8582c90/docs/source/format/Columnar.rst#ipc-streaming-format)
· [Executable API](../../Silmaril/Formats/Arrow/DateStream/Writer/Defs.lean)

The Schema reuses the shared field and vector assemblers. Each record
reuses the checked physical Int32 encoding for validity bits, signed
32-bit words, aligned buffers, RecordBatch metadata and framing.
A null word is stored as zero with a clear validity bit. Empty batches
are emitted as zero-row records, and a schema-only stream ends at the
modern EOS. The signed words cover the full Date32 range. The day scale
matches the existing Gregorian epoch-day model.
[DATE stream reader](arrow-date-stream.md)

The writer checks the Schema metadata size, aggregate row/cell budgets
and batch limits. Record checks report their zero-based record index
and the underlying writer cause. A null in a required field fails the
physical batch shape check. After assembly, the existing checked DATE
reader must recover the exact field and nested batches. It returns a
typed readback error or mismatch if that check fails. Completed IPC
bytes are returned only on success.

`schemaMetadata_size` proves the exact padded Schema metadata extent
used for the preflight. `emit_readback` proves recovery of the exact
field and ordered nullable civil batches, including empties.
`observation_words` recovers the original signed words from that
observation.
[Theorem header](../../Silmaril/Formats/Arrow/DateStream/Writer/Thms.lean)

## Independent oracle

CPython 3.13.5 and PyArrow 26.0.1 generate four pinned reference streams.
PyArrow reads all four Lean-emitted streams and checks exact field name,
logical type, nullability, original signed words, nulls and batch
boundaries. The independent byte checker locates the emitted FlatBuffers
DateUnit, field node and two buffer descriptors. It checks explicit DAY,
each record's padding, the validity bits and exact packed signed words
against Python `struct` encoding. These checks allow PyArrow to choose
its own equivalent wire layout for reference streams.

The cases include UTF-8 labels, both signed endpoints, pre-epoch dates,
year zero, a leap day, bitmap boundaries, optional nulls, a required
field, an empty middle batch, a schema-only stream and a zero-row record.
Lean guards also check missing budgets and a late null in a required
field.
[Fixture hashes](../../scripts/arrow-date32-writer-oracle/fixtures.json)
· [Oracle](../../scripts/arrow-date32-writer-oracle/check.py)

```sh
targets='+Silmaril.Formats.Arrow.DateStream.Writer.Thms +Silmaril.Formats.Arrow.DateStream.Writer.Tests +Silmaril.Formats.Arrow.DateStream.Tests +Silmaril.Formats.Arrow.FileWriter.Axioms arrow_ipc_metadata_tests'
lake build --wfail $targets
make check CHECK_TARGETS="$targets"
lake env lean -DautoImplicit=false -DwarningAsError=true tests/formats/arrow-date32-writer/Axioms.lean
python3 -I scripts/arrow-date32-writer-oracle/check.py
```

Use `--pyarrow-path` for a separately unpacked pinned wheel.
