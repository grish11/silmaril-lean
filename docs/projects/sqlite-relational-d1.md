# SQLite relational values and affinity (Track D1)

Import `Silmaril.Semantics.SQLite.Relational.Value.Thms` for storage values and
C API observations, and `Silmaril.Semantics.SQLite.Relational.Affinity.Thms` for
column declarations and write affinity. Both use `Silmaril.SQLite.Relational`.
The column boundary consumes `SqlValue`, which can serve as a cell carrier for
the Track C relational interfaces. [Value API](../../Silmaril/Semantics/SQLite/Relational/Value/Thms.lean) ·
[Affinity API](../../Silmaril/Semantics/SQLite/Relational/Affinity/Thms.lean) ·
[Track C](relational.md)

## Upstream baseline

SQLite compiles SQL to bytecode. The VDBE runs it and uses `Mem` to represent
values, including representation flags and metadata. D1 models selected
observations at that value boundary and the logical class read back after a
column write. It has no bytecode execution or database-file interpretation.
[SQLite architecture](https://sqlite.org/arch.html) ·
[Datatypes and affinity](https://sqlite.org/datatype3.html) ·
[STRICT tables](https://sqlite.org/stricttables.html)

The source baseline is **SQLite 3.54.1**, source ID
`2026-10-16 14:45:20 555e07ef33f69a0957d24d8e555b702464a131d6f1607f4c3c1e4551e8e6ca76`.
The release archive SHA-256 is
`0a9c8e34352dad46006aa82836d5383bff9dc6bc9ce5a60553c05aa30e6ad1f9`.
The pinned amalgamation `sqlite3.c` SHA-256 is
`0c657666d819f261cc4007526ad57e1669de9949df7a8ea847aa284a2bf0ee52`.
The source cuts are `sqlite3AffinityType` and STRICT declaration handling,
`sqlite3AtoF`, `applyAffinity`, `OP_TypeCheck`, `OP_MakeRecord`, `OP_RealAffinity`,
and the `sqlite3_value_*` functions. [Release archive](https://sqlite.org/2026/sqlite-amalgamation-3540100.zip) ·
[Corpus pins](../../corpus/sqlite/upstream.sha256) ·
[Declaration rules](../../corpus/sqlite/upstream/sqlite-amalgamation-3540100/sqlite3.c#L128492) ·
[Number recognition](../../corpus/sqlite/upstream/sqlite-amalgamation-3540100/sqlite3.c#L37713) ·
[VDBE affinity](../../corpus/sqlite/upstream/sqlite-amalgamation-3540100/sqlite3.c#L96630) ·
[STRICT write check](../../corpus/sqlite/upstream/sqlite-amalgamation-3540100/sqlite3.c#L99714)

## Value observations

| Class | `SqlValue` payload |
| --- | --- |
| NULL | No payload. |
| INTEGER | Lean `Int64`, with signed range −2⁶³ through 2⁶³−1. |
| REAL | Non-NaN IEEE binary64 bits. Signed zeros, subnormals and infinities are representable. `Real.ofBits` rejects NaNs. `SqlValue.ofRealBits` maps them to NULL as SQLite does for a double input. |
| TEXT | A `ByteArray` tagged UTF-8, UTF-16LE or UTF-16BE. The payload retains embedded NULs and may contain ill-formed code units. `Text.utf8` encodes a Lean string without adding a terminator. |
| BLOB | An uninterpreted `ByteArray`. Identical bytes as TEXT and BLOB give distinct values. |

`DecidableEq` compares the modeled representation. REAL equality distinguishes
signed zero, and TEXT equality distinguishes both encoding tags and bytes. SQL
numeric equality, collation, Unicode normalization, transcoding, malformed-text
handling by native APIs, and on-disk serial types are outside this model.
[Value definitions](../../Silmaril/Semantics/SQLite/Relational/Value/Defs.lean) ·
[SQLite double input](../../corpus/sqlite/upstream/sqlite-amalgamation-3540100/sqlite3.c#L86278)

`Value P` carries a storage value with an optional `UInt8` subtype, or a tagged
pointer with opaque payload `P`. Payloads stand for non-null pointer identities.
`Value Empty` excludes the pointer constructor
while still admitting subtyped SQL values. The pointer type tag consists of
bytes before the C string terminator. SQL projects pointers to NULL.
`ValueObject P access` distinguishes protected and unprotected objects.
The modeled `subtypeCode` and `pointer?` readers require `.protectedValue`.
A subtype reader returns `0` for an absent subtype and `112` (ASCII `p`) for a
pointer. A SQL NULL with subtype `112` cannot supply a pointer. A pointer
projection also requires a matching tag. `dup` models a successful protected
copy, dropping pointers and clearing the subtype on NULL. The model abstracts
from C addresses, destructors, locks, reference lifetimes, allocation failures,
and when SQL expression evaluation propagates or discards subtypes.
[SQLite value objects](https://sqlite.org/c3ref/value.html) ·
[Passing pointers](https://sqlite.org/bindptr.html) ·
[Subtype API](https://sqlite.org/c3ref/result_subtype.html) ·
[Value duplication](https://sqlite.org/c3ref/value_dup.html) ·
[Native duplication](../../corpus/sqlite/upstream/sqlite-amalgamation-3540100/sqlite3.c#L93593)

`Value.toSql` retracts the embedding `Value.ofSql`. It commutes with mapping
pointer payloads, forgetting pointers and successful duplication.
`Value.forgetPointers` retracts embedding from `Value Empty` by mapping
`Empty.elim`. The loss witnesses identify a pointer and an ordinary NULL under
pointer erasure, and tagged and untagged NULLs under SQL projection.
[Projection laws](../../Silmaril/Semantics/SQLite/Relational/Value/Thms.lean) ·
[Checked examples](../../Silmaril/Semantics/SQLite/Relational/Value/Examples.lean)

## Column-write boundary

```lean
Affinity.ofDeclaredType : Option String → Affinity
StrictType.ofDeclaredType : Option String → Option StrictType
ColumnType.apply : ColumnType → SqlValue → Except AffinityError SqlValue
```

Declaration helpers take a resolved, NUL-free name after SQL parsing. Ordinary
names use SQLite's ASCII-insensitive substring precedence `INT`, then
`CHAR`/`CLOB`/`TEXT`, then `BLOB`, then `REAL`/`FLOA`/`DOUB`, then NUMERIC.
An absent declaration has BLOB affinity. STRICT recognizes `INT`, `INTEGER`,
`REAL`, `TEXT`, `BLOB` and `ANY`. Primary-key interpretation belongs to the
table boundary.

| Affinity | Modeled conversion |
| --- | --- |
| BLOB | Identity on all values. |
| TEXT | INTEGER becomes signed base-10 UTF-8 text. REAL formatting is unsupported. Other classes pass through. |
| INTEGER / NUMERIC | NUL-free UTF-8 TEXT with an optional ASCII sign, decimal digits and surrounding SQLite ASCII whitespace becomes INTEGER when it fits. Nonnumeric text stays byte-identical, including `0x20` and incomplete exponent forms. Binary64 values become INTEGER if they round-trip exactly through a signed 64-bit integer strictly inside the signed endpoints. Other REAL values, INTEGER, BLOB and NULL pass through. |
| REAL | Applies numeric affinity, then promotes INTEGER to binary64 with round-to-nearest, ties-to-even via Lean's logical float model. This can round an input INTEGER and turns a REAL negative zero into positive zero through integer zero. The resulting REAL class describes logical readback, including values SQLite can store using integer serial types. |

Ordinary `ANY` has NUMERIC affinity, so `TEXT '000123'` becomes `INTEGER 123`.
STRICT `ANY` preserves the original value and its representation. Other STRICT
columns check the post-affinity storage class, with NULL accepted here.
`ColumnType.strict_apply_eq_ok_iff` characterizes successful STRICT writes.
A `.datatype` error is a modeled storage-class mismatch. An `.unsupported`
error leaves the native result unspecified. Unsupported numeric text includes
UTF-16 input, embedded NUL, decimal-point or exponent forms such as `3.0e+5`,
and integer text outside the signed 64-bit range. The UTF-8 profile does not
model a database-wide encoding or conversions to it. SQL literals, CAST,
comparison affinity, row constraints, file representation and allocation
errors are outside this boundary. The statements and examples are about the
Lean model and establish no native equivalence. [Affinity definitions](../../Silmaril/Semantics/SQLite/Relational/Affinity/Defs.lean) ·
[Checked boundary cases](../../Silmaril/Semantics/SQLite/Relational/Affinity/Examples.lean) ·
[SQLite REAL readback](../../corpus/sqlite/upstream/sqlite-amalgamation-3540100/sqlite3.c#L98482)

## Checks

```sh
lake build --wfail +Silmaril.Semantics.SQLite.Relational.Value.Examples \
  +Silmaril.Semantics.SQLite.Relational.Affinity.Examples
base=$(git merge-base HEAD origin/main)
scoped=$(make -s scope BASE="$base")
full=$(make -s scope)
targets=$(python3 scripts/ci-targets.py --scoped "$scoped" --full "$full")
make check CHECK_TARGETS="$targets"
```
