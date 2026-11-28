# Selected flat PLAIN INT32 Parquet columns with Zstandard

`FlatColumn.Zstd.readColumn` reads one footer group for a selected,
required or optional flat PLAIN INT32 leaf of a checked snapshot.
Bind the name and nullability using `FlatColumn.bindColumn`. The
reader admits footer codec 6 and uses the original page frames and
body spans from that snapshot. It uses the same column walk as the
existing codec-0 API. Its indexed error type keeps the original group,
column, page and header offset for callback failures. Errors while
framing a chunk retain the group and column.
[Reader and wire contracts][thms]

V1 gives the whole on-disk body to the checked frame decoder before
reading its level and value sections. V2 validates both declared page
sizes against its raw definition-level extent before subtracting it.
The original prefix supplies the mask, and only the remaining values
are passed to the codec. A true or absent V2 flag uses Zstandard. A
false flag uses the bounded uncompressed identity path, even in a
codec-6 column. The exact input length is checked before dispatch, and
the expected regenerated length is supplied as the output budget.
Successful output has that exact length. Frame window and per-block
command limits are explicit caller inputs.
[Parquet 2.14.0 IDL][idl] · [Compression specification][compression]

`decodePayload_sound` binds the exact codec extent, caps, and decoded
size to the checked Zstandard frame or raw identity. `decodePage_sound`
retains the exact V1 body or V2 raw level prefix and codec-selected
suffix, the declared page extents, and the ordered PLAIN slots.
`readColumn_wire` ties those page relations to the actual selected
codec-6 chunk and the original ordered frame list in the checked
snapshot. [Theorem header][thms]

This is one dictionary-free strict RFC 8878 frame per compressed slice.
It rejects a distance equal to the declared window, which pinned
libzstd accepts. The exact-frame decoder verifies a Zstandard checksum
when present. This selected-column profile rejects Parquet page
CRCs, dictionary and non-data pages, and legacy non-RLE V1 levels.
The bounds concern logical bytes, windows and command counts.
[Frame profile and strict-window differential][zstd]

## Independent fixtures

The oracle uses PyArrow 26.0.1 from
`9e5d6978e9acf372cc989aaaf94e863fe8582c90` and Thrift 0.25.0 from
`27e8a425ffb498e190df3a12e239326bf5ba9ed6`. Thrift reads the numeric
codec IDs and header spans independently. PyArrow supplies the exact
whole-file bytes and decoded nullable-slot order. Each mixed file has
three groups, with optional and required codec-6 columns and a codec-0
column used as an admission control. The large frame has a native
Huffman new tree.

| File | Accepted codec-6 column pages | SHA-256 |
| --- | --- | --- |
| `zstd-plain-v1.parquet` | 12 Zstandard whole bodies | `97449638f05cdf52675ea600b8b2c6dd49cc0bc9683dfcf320275b5c3a4ecf01` |
| `zstd-plain-v2.parquet` | 8 Zstandard and 4 raw suffixes | `19d17d497a8dc92b02f227c1ca2613c91d9861c2d58208ece92a79e2ffd47c3d` |
| `zstd-plain-v2-huffman.parquet` | 1 Huffman payload | `c7ce05794fce1c0682b7ef3501c4206084510826bdd646dfa26c5f85f036ac55` |

The oracle corrupts an actual frame in group 1, column 1, page 1 of
each mixed file and checks the original indexed cause. Groups 0 and 2
continue to return the original slots on independent reads. Further
controls exercise exact physical length, wrong decoded size, both V2
size fields below the level extent, both wrong flag directions, the
absent flag default, and caller input, output, window and command caps.
[Reproduction runner][oracle]

```sh
lake build --wfail +Silmaril.Formats.Parquet.FlatColumn.Zstd.Tests +Silmaril.Formats.Parquet.MixedBooleanFloat.Tests
make check CHECK_TARGETS="$(make -s scope BASE=origin/main)"
python3 -m venv /tmp/parquet-flat-zstd-oracle
/tmp/parquet-flat-zstd-oracle/bin/python -m pip install 'pyarrow==26.0.1' 'thrift==0.25.0'
/tmp/parquet-flat-zstd-oracle/bin/python -I scripts/parquet-flat-zstd/check.py
```

[thms]: ../../Silmaril/Formats/Parquet/FlatColumn/Zstd/Thms.lean
[oracle]: ../../scripts/parquet-flat-zstd/check.py
[zstd]: zstd-huffman-frame.md
[idl]: https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/src/main/thrift/parquet.thrift#L752-L782
[compression]: https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/Compression.md#zstd
