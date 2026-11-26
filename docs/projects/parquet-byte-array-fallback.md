# Checked Parquet BYTE_ARRAY dictionary fallback

`Silmaril.Formats.Parquet.ByteArrayFallback` reads one named optional
physical BYTE_ARRAY leaf of a flat Parquet snapshot. `openFile` reuses
the checked BYTE_ARRAY binding and file limits. `readGroup` uses the
selected leaf's original column ordinal at the requested footer group.
Payload validation covers that column. Present slots contain opaque bytes.

The profile is codec 0, V1 with flat RLE levels or V2 with flat levels.
An optional single leading dictionary page uses PLAIN tag 0. Data frames
use PLAIN tag 0 or RLE_DICTIONARY tag 8, selected from each original
typed header. Tag 8 requires the same chunk's leading dictionary. The
footer encoding list admits only 0, 3 and 8 and must advertise each
actual value tag. Tag 3 is a level encoding in this profile.
The reader rejects CRC-bearing pages, index pages,
nonleading dictionaries, legacy tag 2, and chunks without a data frame.

The reader checks chunk bounds, declared row counts and page and
dictionary limits before materializing the corresponding bodies. It
dispatches once per admitted frame. The first page failure after chunk
framing and count checks carries the original group, column, frame
ordinal, and header offset. A leading dictionary occupies frame ordinal
zero when present. A row group is returned only after all its selected
pages succeed.

`readGroup_wire` ties the original leaf, group, column and
`Page.readChunk` equation to the same immutable snapshot. The leading
dictionary's exact body yields the ordered PLAIN entries. For each
original data frame, the wire relation retains the exact body and
definition mask. The PLAIN branch consumes the exact value suffix and
the dictionary branch relates every ordered index to its original
entry. The resulting nullable slots are concatenated in frame order
and equal the footer group count.

## Fixtures

PyArrow 26.0.1 writes and independently reads two 384-row groups in
each clean file. Both groups select column 1 after an INT32 decoy.
Thrift 0.25.0 inspects the original frame boundaries and counts one
leading PLAIN dictionary, 17 tag-8 data frames and seven tag-0 data
frames in every selected chunk. The two dictionaries differ across
groups, and the rows include nulls and non-UTF-8 bytes.

The three V2 controls leave group 0 readable. In group 1, omitting the
dictionary from the declared span fails at frame 0, header 15111.
Changing a later PLAIN page tag to 3 fails at frame 19, header 16814.
Changing a final PLAIN length word fails at frame 24, header 22513.
PyArrow independently rejects each damaged group.

| File | SHA-256 |
| --- | --- |
| byte-array-fallback-v1.parquet | `7e2daecc0b67ed06ac25902eceaa777378413a0448d3d3872e2d42af52882b09` |
| byte-array-fallback-v2.parquet | `40d4e2f55d2b718bec8eeed69b4d58308ee4199f67e5be4983e9bfdfc339d7ee` |
| byte-array-fallback-v2-missing-dictionary.parquet | `5d73a8ac69fe8490b2e5276bcdceb201986abb8a3b6fa73479ac27140fed5feb` |
| byte-array-fallback-v2-bad-tag.parquet | `ad87729c086fc12f3fed424f6bd7c59b8874ab469ccfb6c8048224d2980faa08` |
| byte-array-fallback-v2-bad-length.parquet | `b70c6c3010fd442210464c9f60f86d1abef3be5f7805cec43179741a2637b8d6` |

```sh
fixture_tmp=$(mktemp -d)
python3 scripts/parquet-byte-array-fallback/Oracle.py "$fixture_tmp"
diff -r data/parquet-byte-array-fallback "$fixture_tmp"
lake build --wfail +Silmaril.Formats.Parquet.ByteArrayFallback.Tests
lake env lean -DautoImplicit=false -DwarningAsError=true tests/formats/parquet-byte-array-fallback/Axioms.lean
```
