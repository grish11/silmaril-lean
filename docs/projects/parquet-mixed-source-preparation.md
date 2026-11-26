# Prepare checked INT32 and BYTE_ARRAY groups for mixed Arrow batches

`Parquet.Int32ByteArrayGroup.Prepare.prepare` takes immutable Parquet
bytes, the checked whole-file reader's limits, and two explicit field
selections. It opens and consumes the bounded selected source from
`Int32ByteArrayGroup.File`. The prepared schema contains the exact
INT32 then BinaryView names and required or optional flags. It is
separate from the batch list, including on a schema-only input.
[Checked file source](parquet-int32-byte-array-file.md)

Each footer group becomes one prepared batch with its own row count
and two ordered nullable lists. A row position carries the original
signed INT32 and opaque octets. The byte trees preserve empty values,
embedded zero and non-UTF-8 octets. An admitted empty group keeps
its position and contributes two empty lists. The result can feed a
checked mixed stream writer's separate schema and batch inputs.

`prepare_ok_iff` characterizes checked open, ordered indexed reads and
the exact prepared result. `prepare_exact` gives both descriptors,
the exact footer group count, and the paired per-group slot laws.
`prepare_open_error` and `prepare_first_error` preserve the original
source cause, including the first failed group's nested selected-column,
page and header offset when present. The independent source trace
still contains the complete earlier batches. The preparation result
is all-or-error and carries typed data for a consumer.
[Theorem header](../../Silmaril/Formats/Parquet/Int32ByteArrayGroup/Prepare/Thms.lean)

## Independent verification

CPython 3.13.5, PyArrow 26.0.1 and Thrift 0.25.0 reproduce seven
pinned inputs. The existing V1 and V2 fixtures have different page
cuts in their selected columns. The oracle also checks an intact
selection from a file with an unselected corrupt chunk, the framed
`[3, 0, 2]` fixture, a new optional INT32 and required BYTE_ARRAY
fixture with signed endpoints, and a schema-only file. It compares
each prepared descriptor, row count and paired nullable slot
against PyArrow's selected columns in the original group order.
[Fixture pins](../../scripts/parquet-mixed-preparation-oracle/sha256.json)

Eight typed controls cover byte-cap precedence, selection before the
footer row cap, the row cap before selected decoding, and the first
indexed failure after admission. The empty-middle corruption retains
`[3, 0]` in the separate trace and reports group 2, column 1, page 0,
header byte 108.

```sh
lake build --wfail +Silmaril.Formats.Parquet.Int32ByteArrayGroup.Prepare.Checks
lake env lean -DautoImplicit=false -DwarningAsError=true Silmaril/Formats/Parquet/Int32ByteArrayGroup/Prepare/Checks.lean
python3.13 -B scripts/parquet-mixed-preparation-oracle/check.py --out /tmp/parquet-mixed-preparation
```

[Parquet Format 2.14.0 encodings](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/Encodings.md) ·
[Arrow 26.0.1 BinaryView](https://github.com/apache/arrow/blob/9e5d6978e9acf372cc989aaaf94e863fe8582c90/docs/source/format/Columnar.rst)
