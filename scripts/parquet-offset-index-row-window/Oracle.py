"""Read pinned Thrift index locations and compare independent PyArrow row slices."""

from hashlib import sha256
from pathlib import Path
import runpy
import struct

import pyarrow as pa
import pyarrow.parquet as pq

V2_SHA256 = "4433b34caef2f7c53c1b6cd0a94c5f6e3b748c4b830df633b96b40855e46f401"
UNINDEXED_SHA256 = "7b1053e77957f849fd6c72fbfb9e8260037ae20dfa2d0d550b3b97f7014ba915"
WINDOWS = {
    (3, 10): ([(112, 36, 3, 4), (148, 40, 0, 4), (188, 36, 0, 2)], [None, 29, 32, 35, 38, None, 44]),
    (4, 8): ([(148, 40, 0, 4)], [29, 32, 35, 38]),
    (10, 15): ([(188, 36, 2, 4)], [47, 50]),
    (0, 15): (
        [(112, 36, 0, 4), (148, 40, 0, 4), (188, 36, 0, 4)],
        [17, 20, 23, None, 29, 32, 35, 38, None, 44, 47, 50],
    ),
    (0, 0): ([], []),
    (8, 4): ([], []),
    (12, 15): ([], []),
    (13, 15): ([], []),
}


def main():
    assert pa.__version__ == "26.0.1"
    root = Path(__file__).resolve().parents[2]
    path = root / "data/parquet-offset-index/v2-index.parquet"
    unindexed = root / "data/parquet-offset-index/v1-no-index.parquet"
    thrift = runpy.run_path(str(root / "scripts/parquet-offset-index/reproduce.py"))
    data = path.read_bytes()
    assert sha256(data).hexdigest() == V2_SHA256
    assert sha256(unindexed.read_bytes()).hexdigest() == UNINDEXED_SHA256
    thrift["check"](path, "2.0", indexed=True)
    thrift["check"](unindexed, "1.0", indexed=False)

    footer_size = struct.unpack("<I", data[-8:-4])[0]
    footer, _ = thrift["parse"](data[-8 - footer_size:-8], thrift["FOOTER"])
    selected = footer[4][1]
    [column] = selected[1]
    offset, size = column[4], column[5]
    index, consumed = thrift["parse"](data[offset:offset + size], thrift["OFFSET_INDEX"])
    assert consumed == size
    locations = index[1]
    group = pq.ParquetFile(path).read_row_group(1)
    assert len(group) == selected[3] == 12
    starts = [location[3] for location in locations] + [len(group)]
    for (first, stop), (expected, expected_values) in WINDOWS.items():
        pieces = []
        for location, start, end in zip(locations, starts[:-1], starts[1:], strict=True):
            selected_rows = [local for local, row in enumerate(range(start, end)) if first <= row < stop]
            if selected_rows:
                pieces.append((location[1], location[2], selected_rows[0], selected_rows[-1] + 1))
        values = group.slice(first, max(0, stop - first)).column(0).to_pylist()
        assert pieces == expected and values == expected_values
        print(f"[{first}, {stop}) -> {pieces} -> {values}")


if __name__ == "__main__":
    main()
