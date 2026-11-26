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

## Selected whole-file events

`Silmaril.Formats.Parquet.ByteArrayFallback.File.Defs` exposes
`openSource` and `readAll` for the same named optional leaf. `openSource`
uses the checked fallback open and its file byte and total row caps,
then supplies the common `Reader.Source` with the original footer
ordinals and the existing opaque BYTE_ARRAY row mapping. It can also
be consumed through `Reader.batchReader`.

The trace has one batch for each completely read group. An admitted
zero-row group contributes an empty batch in its original position.
The first failure keeps the preceding batches and carries the
original `ByteArrayFallback.Error` in `File.Error.readFailure`.
`File.readAll_order`, `File.readAll_success`, `File.readAll_first_error`
and `File.batch_slots` state these contracts.

The source tests reuse the five fallback fixtures for exact `[384, 384]`
batches and the original indexed errors after `[384]`. A total cap of
767 on the damaged 768-row files fails at open. The existing
[framed empty-middle fixture](parquet-int32-byte-array-file.md#producer-fixtures)
gives `[3, 0, 2]` at EOS and `[3, 0]` when the final group's binary
tag is changed to 3.

```sh
lake build --wfail +Silmaril.Formats.Parquet.ByteArrayFallback.File.Tests
lake env lean -DautoImplicit=false -DwarningAsError=true tests/formats/parquet-byte-array-fallback-file/Axioms.lean
```

## Opt-in parquet-java V1 fallback

`ByteArrayFallback.readLegacyGroup` uses the checked optional BYTE_ARRAY
binding and the existing bounded chunk walk for codec 0. It admits the
parquet-java V1 combination of a leading tag-2 dictionary and data tags
2 and 0. The dictionary body contains PLAIN length-prefixed entries.
Data pages use V1 definition tag 3 and repetition tag 4. The matched
flat leaf has maximum repetition level zero, so the existing scalar
adapter receives tag 3 for that absent repetition section.
`legacy_parameters_wire` relates this adapter parameter to the original
header and preserves the value tag, sizes and count. `readLegacyGroup_wire`
retains the original selected snapshot, ordered frames, chunk-local
dictionary lookups and PLAIN suffixes.

The producer is parquet-java 1.16.0, commit
`402c3810c372d29603e181771acebfecc71bef61`. The Thrift 0.25.0 oracle
sorts the footer encoding lists because parquet-java serializes them
in JVM-dependent order. All original page bytes and offsets are
preserved. The selected chunk's dictionary header is at byte 1900.
Its data section begins at 1937 and has ten tag-2 pages followed by
nine tag-0 pages. PyArrow 26.0.1 reads all 384 original slots and
rejects the damaged final PLAIN length. Lean reports the damage at
group 0, column 1, frame 19, header byte 10089.

| File | SHA-256 |
| --- | --- |
| parquet-java-v1-legacy-fallback.parquet | `63231c6286d24acc8ff3fcbf72b0641fb861dd7a78eec9908899cc9b14c07135` |
| parquet-java-v1-legacy-fallback-bad-length.parquet | `ba08f3886655f91c488e2b8e93b9bccca4ef87eb5ec4d1dbb0126cbd78dde9a1` |

Run from the repository root with JDK 21, Maven, PyArrow 26.0.1 and
Thrift 0.25.0.

```sh
fixture_tmp=$(mktemp -d)
mvn -B -q -f scripts/parquet-dictionary-chunk/pom.xml \
  org.apache.maven.plugins:maven-dependency-plugin:3.8.1:build-classpath \
  -Dmdep.outputFile="$fixture_tmp/classpath"
java -cp "$(cat "$fixture_tmp/classpath")" scripts/parquet-byte-array-legacy-fallback/WriteFallback.java "$fixture_tmp"
python3 scripts/parquet-byte-array-legacy-fallback/Oracle.py "$fixture_tmp"
for fixture in data/parquet-byte-array-legacy-fallback/*.parquet; do
  cmp "$fixture" "$fixture_tmp/$(basename "$fixture")"
done
lake build --wfail +Silmaril.Formats.Parquet.ByteArrayFallback.LegacyTests
```

### Legacy whole-file events

`ByteArrayFallback.File.openLegacySource` and `readAllLegacy` select the
parquet-java V1 profile through the same checked source and file limits.
`readAllLegacy_success` preserves one batch per successfully decoded
footer group and its opaque slots. `readAllLegacy_first_error` preserves
the preceding complete batches and wraps the original indexed cause
in `File.Error.readFailure`. An admitted zero-row group emits its own
empty batch before the next footer group.

The Thrift 0.25.0 oracle copies the pinned parquet-java 1.16.0 chunk
bytes into groups 0 and 2 and supplies explicit zero-row PLAIN V1
frames for group 1. It relocates the chunk offsets and omits the
detached page indexes. The producer page headers and bodies in both
nonempty groups are byte-identical to the pinned source. PyArrow 26.0.1
independently checked the slots and group counts.

The clean fixture emits `[384, 0, 384]` and EOS. The damaged fixture
changes only the final PLAIN value length and emits `[384, 0]` before
the original error at group 2, column 1, frame 19, header byte 21009.
A total cap of 767 on that 768-row file fails at open.

| File | SHA-256 |
| --- | --- |
| legacy-v1-empty-middle.parquet | `67a4029e7ff4afcd9e3c88e1a335d22e4c52ef9d16ebd9e324b61e935d1e91a5` |
| legacy-v1-late-error.parquet | `58a6f17e3547e743c6dad6c66d4306a9f843875ecb438862bbd36e0c44036a77` |

```sh
fixture_tmp=$(mktemp -d)
python3 scripts/parquet-byte-array-legacy-events/Oracle.py "$fixture_tmp"
diff -r data/parquet-byte-array-legacy-events "$fixture_tmp"
lake build --wfail +Silmaril.Formats.Parquet.ByteArrayFallback.File.LegacyTests
lake env lean -DautoImplicit=false -DwarningAsError=true tests/formats/parquet-byte-array-fallback-file/Axioms.lean
```
