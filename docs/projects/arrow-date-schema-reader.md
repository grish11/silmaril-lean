# Arrow V5 DATE Schema metadata reader

`Silmaril.Formats.Arrow.SchemaReader.readMessage` reads a V5 Schema message
metadata slice with zero body length. It returns ordered fields with names,
nullability, checked type parameters, and the schema's Little or Big endianness.
The parser uses the existing private FlatBuffers table, slot, vector, and
reference checks. Its type dispatch admits the existing signed Int32 and Utf8
profile plus DATE. [Arrow IPC and Columnar format](https://github.com/apache/arrow/blob/9e5d6978e9acf372cc989aaaf94e863fe8582c90/docs/source/format/Columnar.rst)

The pinned `Schema.fbs` Type union assigns DATE tag 8. Its unit is a short,
with explicit DAY encoded as 0 and MILLISECOND as 1. An omitted DateUnit slot
defaults to MILLISECOND. The normalization laws characterize accepted codes and
reject other codes. An omitted schema endianness defaults to Little. A declared
Big endian is preserved in the metadata result, and the existing body reader
still applies its little-endian admission policy. [Arrow 26.0.1 Schema.fbs](https://github.com/apache/arrow/blob/9e5d6978e9acf372cc989aaaf94e863fe8582c90/format/Schema.fbs)
· [Normalization laws](../../Silmaril/Formats/Arrow/Metadata/Thms.lean)

`Arrow.readMessage` and the existing `Arrow.FieldType` remain the
Int32/Utf8 reader and writer API. Both read paths use the same common metadata
checks. The additive Schema reader selects a separate normalized field type.
A DATE consumer can use the field's normalized unit code and nullability with
the schema endianness code. DATE body decoding and complete DATE stream or
file admission are separate layers. The [checked DATE batch binding](arrow-date-batch.md)
composes the Schema and body readers for one DATE column. Future Timestamp metadata can use the same
private type-payload dispatch.

## Verification

The harness pins CPython 3.13.5, PyArrow 26.0.1, and the generated metadata
hashes. It checks the presence of the producer's explicit DAY slot and the
absence of the MILLISECOND slot, then compares the ordered Schema observation
with PyArrow. Other fixtures cover explicit MILLISECOND, Big endian metadata,
unknown unit, endian and type codes, and the existing legacy reader's
admission. A mutation changes a real Int32 field's tag to DATE and checks that
the reader rejects its two-slot Int32 payload table. The union tag selects
the layout, and the checks validate the payload against that layout.

Two pinned single-column streams use the parsed Schema date unit,
endianness and nullability to select and call `DateValues.decodeBatch`.
Both match PyArrow's ordered nullable civil dates. The hosted Lean test
includes the two-field Schema and the Date32 schema-to-batch fixture.
[Fixture manifest](../../scripts/arrow-date-schema-oracle/fixtures.json)

```sh
targets='+Silmaril.Formats.Arrow.DateBatch.Defs +Silmaril.Formats.Arrow.Metadata.Thms +Silmaril.Formats.Arrow.Metadata.Tests +Silmaril.Formats.Arrow.Writer.Thms +Silmaril.Formats.Arrow.StreamWriter.Thms arrow_ipc_metadata_tests'
lake build --wfail $targets
make check CHECK_TARGETS="$targets"
python3 -I scripts/arrow-date-schema-oracle/check.py
```

Use `--pyarrow-path` when the pinned wheel was unpacked outside the Python
environment.
