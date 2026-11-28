# Parquet TIMESTAMP to typed Arrow events

`Silmaril.Formats.Parquet.Timestamp.Leaf.Events.batchReader` opens one
checked Parquet snapshot and selects one flat modern INT64 TIMESTAMP leaf
by serialized schema-node ordinal (root at zero). The Arrow event schema
keeps that leaf's name and nullability. Every pull uses the retained
binding and the existing checked selected-group decoder.
[Selected leaf profile](parquet-timestamp-leaf.md) ·
[Arrow event API](../../Silmaril/Formats/Arrow/Events/Defs.lean)

Parquet MILLIS, MICROS and NANOS map to the same Arrow unit.
`isAdjustedToUTC=true` gives the Arrow annotation `some "UTC"` and the
UTC instant interpretation. `false` gives `none` and the local reading
interpretation. A present cell carries its original signed count and each
null remains null. The mapping performs no rescaling, offset arithmetic,
or timezone database resolution.
[Parquet 2.14.0 TIMESTAMP](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/LogicalTypes.md#timestamp) ·
[Arrow 26.0.1 Schema IDL](https://github.com/apache/arrow/blob/9e5d6978e9acf372cc989aaaf94e863fe8582c90/format/Schema.fbs)

`readAll` emits one batch per successful footer row group, including
groups decoded to zero slots, in ascending zero-based footer order. A
failed open has no schema. A failed group read terminates with its exact
index and binder cause and preserves the preceding complete batches.
Collection concatenates the rows while preserving schema and termination.
A bounded pull can close the unread suffix. This adapter emits abstract
events from a bounded in-memory snapshot. IPC serialization and tables or
CSV belong to a separate layer. All source admission, including legacy
tag policy and the supported PLAIN page profile, comes from the binder.

## Public contracts

- `metadata_exact` and `schema_field` give the full one-field schema mapping.
- `batch_slots` preserves the length and exact ordered nullable signed counts.
- `readAll_reference` equates the trace with the reference reads over the
  binder, including batch boundaries and terminal outcome.
- `collect_readAll` equates the collected observation with the ordered
  concatenation of those reference groups and their terminal outcome.
- `readAll_open_error` and `readAll_first_error` identify the typed
  failure and, for a group failure, its complete successful prefix.

[Theorem header](../../Silmaril/Formats/Parquet/Timestamp/Leaf/Events/Thms.lean)

## Independent fixtures

CPython 3.13.5 with PyArrow 26.0.1 writes six Parquet 2.6 files with
uncompressed PLAIN V2 pages, three groups per file, and both adjusted
and local timestamps at each of the three units. The fixtures cover mixed
nulls, a required leaf, negative counts and both signed Int64 endpoints.
PyArrow independently reads each group's schema and signed values. For
the middle, empty group, PyArrow writes a zero-size chunk at offset zero.
The checked binder requires a real chunk span, so a Thrift 0.25.0 edit
attaches a zero-row PLAIN V2 header with an empty payload and updates the
footer span. The pinned edited files exercise empty-batch preservation
without relaxing the binder's profile.

A second Thrift edit changes the final local-microsecond group's page
from PLAIN to RLE_DICTIONARY without a dictionary. PyArrow reads both
preceding groups and rejects the damaged last group. Silmaril checks the
exact terminal error, retained batches and collected rows. The oracle
also tests bounded close after the empty group and a typed root-selection
open failure.
[Generator and oracle](../../tests/formats/parquet-timestamp-events/check-fixtures.py) ·
[Fixture SHA-256 pins](../../tests/formats/parquet-timestamp-events/fixtures.json)

```sh
targets='+Silmaril.Formats.Parquet.Timestamp.Leaf.Events.Thms +Silmaril.Formats.Parquet.Timestamp.Leaf.Thms +Silmaril.Formats.Parquet.Date.Events.Tests parquet-flat-scan-regression parquet-page-regression parquet-footer-regression'
lake build --wfail +Silmaril.Formats.Parquet.Timestamp.Leaf.Events.Thms
make check CHECK_TARGETS="$targets"
lake env lean -DautoImplicit=false -DwarningAsError=true tests/formats/parquet-timestamp-events/Axioms.lean
python3 -m venv /tmp/parquet-timestamp-events
/tmp/parquet-timestamp-events/bin/pip install --no-deps --require-hashes -r tests/formats/columnar-timestamp-wire/requirements.txt
/tmp/parquet-timestamp-events/bin/python -I tests/formats/parquet-timestamp-events/check-fixtures.py
```
