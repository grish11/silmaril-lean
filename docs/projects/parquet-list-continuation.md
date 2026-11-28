# Multi-page Parquet V1 LIST continuation

`ListFile.Multi.readAll` and `openSource` admit the same canonical nullable
`LIST<nullable INT32>` footer and one local column per row group as the
[singleton reader](parquet-list-file.md). A chunk may contain several
CRC-free, uncompressed PLAIN V1 data frames. The full checked chunk is
framed before scalar decoding. Each frame owns its level lengths, level
slots and scalar extent. A frame beginning within a row appends its
elements to the existing open list. A group starts without an open
list, and finishing the group closes any last open list.

Data Page V1 permits a page to begin with a nonzero repetition level
when there is no OffsetIndex. A present OffsetIndex requires every page
to start on a row boundary. The reader enforces that rule and does not
use the index contents. The V2 page contract has a different boundary
rule and is outside this profile.
[Pinned V1 and V2 rules](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/src/main/thrift/parquet.thrift#L697-L762)

`ListPage.decodeV1Events` checks the page's exact bytes independently of
neighboring pages. `State.feed` accepts a continuation only when a
nonempty list is open. The first element of that list may itself be
null. Null and empty list events close any prior open list, so neither
can be continued. `feed_wire` and `feed_append` prove that the finished
state re-emits the exact original event sequence and that cutting that
sequence between pages leaves the state result unchanged.
[State and page contracts](../../Silmaril/Formats/Parquet/ListPage/Thms.lean)

`Multi.readGroup_wire` ties the frame sequence to the original
immutable snapshot, group and physical chunk. It accounts for the
chunk's complete footer slot count and the group's row count, and
shows that the rows re-emit the concatenated page events in frame
order. The existing file, framing and per-page limits apply. The
footer row count and a new group slot cap are checked before decoding,
and each frame is charged against the remaining advertised slots
before its payload is sliced. The group slot cap bounds accumulation
even when a corrupt stream has more list starts than the declared rows.
Frame-local errors retain the zero-based page ordinal and absolute
header offset. Earlier framing failures retain the original typed
framing cause. The Arrow trace retains the original group ordinal
and earlier successful batches.
[Group and event contracts](../../Silmaril/Formats/Parquet/ListFile/Multi/Thms.lean)

The original `ListFile` entry points still require a singleton frame.
The new entry points stay within the canonical LIST shape and abstract
Arrow Events carriers. Additional nested layouts, codec support,
scanner routing, and Arrow IPC are outside this change.

## Native and authored fixtures

Pinned PyArrow 26.0.1 emits four V1 pages at row boundaries, with and
without an OffsetIndex. Each file contains a null list, an empty list,
and two lists containing a value and a null element. The comparator
checks both native files with PyArrow and Thrift 0.25.0.

The authored fixture changes the first repetition bit of the last
page of the unindexed native file and adjusts both footer row counts.
Frame extents, definition levels, slot totals and PLAIN values stay
the same. Thrift and independent bit unpacking verify the original
page boundaries and the repetition levels. PyArrow independently
decodes the authored file as `[None, [], [11, None, 22, None]]`.
The pinned producer produced row-aligned pages in this configuration.

Lean checks both native files and the authored continuation. Refusals
cover continuation on the first frame, after an empty list and with an
OffsetIndex, mismatched slot and row totals, configured caps, and the
original singleton refusal. A corrupt late group in the prior fixture
retains the first complete Arrow batch.
[Fixture hashes and exact byte positions](../../scripts/parquet-list-continuation/observations.txt) · [Pinned producer dependencies](parquet-column-index.md#pinned-independent-fixture)

```sh
set -o pipefail
replay=$(mktemp -d)
python3 scripts/parquet-list-continuation/Oracle.py "$replay" |
  diff -u scripts/parquet-list-continuation/observations.txt -
for name in native-v1 native-indexed-v1 authored-continuation-v1; do
  cmp "data/parquet-list-continuation/$name.parquet" "$replay/$name.parquet"
done
lake build --wfail +Silmaril.Formats.Parquet.ListFile.Multi.Examples +Silmaril.Formats.Parquet.ListFile.Examples +Silmaril.Formats.Parquet.ListPage.Examples
make check CHECK_TARGETS="+Silmaril.Formats.Parquet.ListFile.Multi.Examples +Silmaril.Formats.Parquet.ListFile.Examples +Silmaril.Formats.Parquet.ListPage.Examples"
```
