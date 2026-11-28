# Observational interchange for mixed named imports

[`imports_agree_iff`][theorems] compares a selected checked
[Parquet → IPC → named table import][parquet] with a direct mixed
[IPC → named table import][ipc]. The Parquet source is the existing
uncompressed flat PLAIN INT32 and BYTE_ARRAY V1/V2 profile. The direct
IPC stream must have the exact projected names, nullability and order,
with Int32 first and BinaryView second. The theorem uses the same
starting database and vacant key for both paths.

Under those conditions, successful Parquet conversion within its IPC
import cap and a successful direct IPC observation imply that both
imports succeed. Their returned databases are equal exactly when the
original checked Parquet groups and the direct IPC batches have the
same flattened sequence of signed Int32 and nullable opaque octet pairs.
Order and multiplicity matter. Null, empty octets and an embedded zero
remain distinguishable. The Parquet-to-IPC bridge keeps each footer
group as a batch. The named table stores flattened rows, so different
batch plans can produce the same table, including schema-only versus
one explicit empty batch on an empty source.

The direct IPC limits apply to the supplied stream. The Parquet path
also needs file, group and page admission before native IPC emission.
Its cap applies to the actual internally emitted carrier. Rechunking
can change sizes and budget admission. The law conditions on those
checks and makes no assertion that the two paths accept the same limits
or return the same errors.

Main's checked [Parquet file writer][writer] emits INT32 leaves. The
mixed named [IPC export][export] writes Int32 and BinaryView IPC with
caller-selected batch sizes. Neither API emits a mixed Parquet file.

The [oracle][oracle] reuses the seven pinned Parquet inputs and compares
three selections with five independently emitted PyArrow 26.0.1 IPC
streams. Three pairings import equal tables despite different batch
shapes. Reordered rows and null changed to empty bytes import distinct
tables. The coalesced IPC stream also fits a carrier cap that the larger
Parquet-derived IPC stream exceeds. All five IPC outputs have pinned
hashes and exact PyArrow readback.

```sh
lake build --wfail +Silmaril.Formats.Relational.NamedTable.MixedIpc.Interchange.Checks
python3.13 scripts/mixed-named-interchange-oracle/check.py --out /tmp/mixed-named-interchange
```

[theorems]: ../../Silmaril/Formats/Relational/NamedTable/MixedIpc/Interchange/Thms.lean
[parquet]: parquet-mixed-named-import.md
[ipc]: arrow-mixed-named-table.md
[writer]: ../../Silmaril/Formats/Parquet/FlatInt32Writer/Defs.lean
[export]: arrow-mixed-named-export.md
[oracle]: ../../scripts/mixed-named-interchange-oracle/check.py
