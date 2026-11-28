# Atomic named import of nullable octets

`NamedTable.Binary.importParquet` imports one explicitly selected flat,
uncompressed PLAIN BYTE_ARRAY leaf through the checked whole-file reader.
The caller supplies the selected field and the expected destination field.
The selected name and required or optional layout control the Parquet
binding. `NamedTable.Binary.importIpc` consumes one checked BinaryView IPC
V5 field through explicit EOS. The database uses the existing
`NamedTable.Packed` and the shared raw-octet observation. Null, an empty
value, an embedded zero, and non-UTF-8 octets retain their original
meaning and position. [Parquet reader](parquet-plain-byte-array-file.md) ·
[Shared binary observation](binary-file-observation.md)

Both entry points use `NamedTable.importCollected`. A vacant destination,
successful exhaustion, and an exact descriptor are required to return a
replacement database. The returned database changes only the requested
key. Equal exhausted observations give equal updates from the same
database and destination. Rechunking does not affect the update when row
order stays equal. Reordering the rows changes the stored sequence.
[Named gate](../../Silmaril/Formats/Relational/NamedTable/Defs.lean) ·
[Theorem header](../../Silmaril/Formats/Relational/NamedTable/Binary/Thms.lean)

An occupied name returns `nameConflict`. For a vacant name, a Parquet
selection failure returns its original open cause, and a mismatch
between the observed and expected descriptor at EOS returns
`schemaMismatch`. A late Parquet error carries its original indexed
cause and the collected source still contains the preceding complete
rows. IPC open and indexed batch errors retain their original causes.
A checked Utf8View stream is outside the raw BinaryView profile.
The abstract gate also rejects a closed observation or a close error,
including one with completed rows. Any error leaves the caller's original
database as the committed state.

## Independent verification

CPython 3.13.5, PyArrow 26.0.1 and Apache Thrift 0.25.0 reproduce
the five pinned inputs. The selected second leaf uses uncompressed
PLAIN V2 and groups of 4 and 4 rows. The independent BinaryView stream
uses batches of 2, 0 and 6 rows. Lean checks equal updates in a database
with existing rows, then checks a stream whose batches appear in
reverse order. The controls exercise repeated insertion, occupied
names with invalid inputs, exact name and nullability, unsupported
Utf8View, open and close outcomes, a late Parquet length failure and
missing IPC EOS. The late Parquet failure is at group 1, column 1,
page 0, header byte 136. [Original fixture pins](../../scripts/binary-file-observation-oracle/sha256.json) ·
[Reordered and Utf8View pins](../../scripts/binary-named-import-oracle/sha256.json)

```sh
lake build --wfail +Silmaril.Formats.Relational.NamedTable.Binary.Checks
lake env lean -DautoImplicit=false -DwarningAsError=true Silmaril/Formats/Relational/NamedTable/Binary/Checks.lean
python3.13 scripts/binary-named-import-oracle/check.py --out /tmp/binary-named-import
```
