"""Check independent PLAIN fixtures and reproducible late corruption."""

from hashlib import sha256
from pathlib import Path
from runpy import run_path
import struct

import pyarrow as pa
import pyarrow.parquet as pq

INDEXED = "e23639cd6be43674fffb7a59072cff7b106665b16129e7439564b35ca1ac3e2e"
UNINDEXED = "7b1053e77957f849fd6c72fbfb9e8260037ae20dfa2d0d550b3b97f7014ba915"
BAD_INDEX = "32c237f248472db0068a73b76ff8c5a8d4c8856a792e940932b318e521f23c53"
BAD_BODY = "44e779d52974743f195779a73135bdccc341edaa427f4e548dfb9d25bae733f0"
BAD_BODY_AND_INDEX = "5943b26d485ad0bfc1279e920bac3d175a28011f4f73f5273fe54d51e01a6842"
GROUP = 1


def parquet(data):
    return pq.ParquetFile(pa.BufferReader(data))


def group_rows(data, group=GROUP):
    return parquet(data).read_row_group(group).column(0).to_pylist()


def main():
    root = Path(__file__).resolve().parents[2]
    assert pa.__version__ == "26.0.1"
    fixture = root / "data/parquet-offset-index/v1-index.parquet"
    unindexed = root / "data/parquet-offset-index/v1-no-index.parquet"
    source, absent = fixture.read_bytes(), unindexed.read_bytes()
    assert sha256(source).hexdigest() == INDEXED
    assert sha256(absent).hexdigest() == UNINDEXED
    thrift = run_path(str(root / "scripts/parquet-offset-index/reproduce.py"))
    thrift["check"](fixture, "1.0", indexed=True)
    thrift["check"](unindexed, "1.0", indexed=False)

    footer_size = struct.unpack("<I", source[-8:-4])[0]
    footer, _ = thrift["parse"](source[-8 - footer_size:-8], thrift["FOOTER"])
    [column] = footer[4][GROUP][1]
    offset, size = column[4], column[5]
    locations, consumed = thrift["parse"](source[offset:offset + size], thrift["OFFSET_INDEX"])
    assert consumed == size
    assert [(page[1], page[2], page[3]) for page in locations[1]] == [(109, 35, 0), (144, 39, 4), (183, 35, 8)]

    rows = group_rows(source)
    assert rows[3:10] == [None, 29, 32, 35, 38, None, 44]
    assert group_rows(absent) == rows

    bad_index = bytearray(source)
    assert bad_index[356] == 218
    bad_index[356] = 220
    assert sha256(bad_index).hexdigest() == BAD_INDEX
    parsed, consumed = thrift["parse"](bad_index[offset:offset + size], thrift["OFFSET_INDEX"])
    assert consumed == size and parsed[1][0][1] == 110
    assert group_rows(bytes(bad_index)) == rows

    last = locations[1][-1]
    start, width = last[1], last[2]
    header, header_width = thrift["parse"](source[start:start + width], thrift["PAGE"])
    body = start + header_width
    assert last[3] == 8 and body == 200 and source[body] == 2
    for original, expected_hash in ((source, BAD_BODY), (bad_index, BAD_BODY_AND_INDEX)):
        corrupted = bytearray(original)
        corrupted[body] = 255
        assert sha256(corrupted).hexdigest() == expected_hash
        assert thrift["parse"](corrupted[start:start + width], thrift["PAGE"]) == (header, header_width)
        assert group_rows(bytes(corrupted), 0) == group_rows(source, 0)
        try:
            group_rows(bytes(corrupted))
        except (OSError, pa.ArrowInvalid) as error:
            assert "invalid number of bytes" in str(error)
        else:
            raise AssertionError("corrupt group remained readable")
    print(f"bad-index {BAD_INDEX}")
    print(f"late-body-corruption {BAD_BODY}")
    print(f"late-body-and-index-corruption {BAD_BODY_AND_INDEX}")
    print(f"Clean group 1 window [3, 10): {rows[3:10]}")
    print("No index and the 110-for-109 index mutation preserve the full PyArrow group rows.")
    print("The later-page body mutation preserves the last frame header and PyArrow rejects group 1.")


if __name__ == "__main__":
    main()
