# Named tables over typed UTF-8 CSV

Import `Silmaril.Formats.Csv.NamedTable.Utf8.Defs` for `importCsv` and
`exportCsv`. They use the existing packed named-table database, explicit
ordered schema, and caller-supplied cell codecs. Export returns the observed
schema alongside the canonical CSV bytes. Use `Typed.Utf8.string` for UTF-8
strings and `Typed.Codecs.int32` for signed canonical decimal. The strict
ASCII entry points remain `Silmaril.Formats.Csv.NamedTable.importCsv` and
`Silmaril.Formats.Csv.NamedTable.exportCsv`. [Typed UTF-8 CSV and wire limits](typed-utf8-csv.md)

- Import uses the existing name-conflict policy. At a vacant name it decodes
  the complete file under the declared schema, including exact header and
  row-width checks. It then compares the declared schema with the expected
  schema, including each ordered label and kind. A decode failure returns
  `openError`, and a schema disagreement after successful decoding returns
  `schemaMismatch`. Both results carry no updated database.
- Export observes the named table and uses its original schema. A missing
  name returns `missingName`. A failed typed or wire encoding returns
  `encodeError`. The wire profile admits valid non-ASCII UTF-8 in labels
  and text, along with the existing CSV field and quoting rules.
- The typed format distinguishes null (`N`), present empty text (`T`),
  and present literal text `N` (`TN`). Zero-column tables use one
  physical empty-field record per logical row plus the header marker.

`importCsv_ok_iff` gives the exact successful update at one vacant name.
`importCsv_decode_error` and `importCsv_schema_mismatch` give the exact
failure results. `decode_exportCsv` and `import_exportCsv` recover the
original schema and ordered rows after successful export, provided every
cell codec satisfies parse-after-print. The latter theorem characterizes the
destination update and preserves every other binding. [Named UTF-8 CSV theorem header](../../Silmaril/Formats/Csv/NamedTable/Utf8/Thms.lean)

The API works at the named-table boundary. Arrow IPC decoding and Arrow schema
translation are separate composition steps.

```sh
targets='+Silmaril.Formats.Csv.NamedTable.Examples +Silmaril.Formats.Csv.NamedTable.Utf8.Examples +Silmaril.Formats.Csv.Typed.Utf8.Tests'
lake build --wfail $targets
make check CHECK_TARGETS="$targets"
python3 -I scripts/typed-utf8-csv-oracle/check.py
```
