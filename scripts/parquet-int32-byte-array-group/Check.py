"""Check projected pairs and page partitions in the pinned #4806 producer files."""

from importlib.metadata import version as package_version
from pathlib import Path
from runpy import run_path
import struct
import sys

import pyarrow as pa
import pyarrow.parquet as pq
from thrift.protocol.TCompactProtocol import TCompactProtocol
from thrift.transport.TTransport import TMemoryBuffer

assert package_version("pyarrow") == "26.0.1"
assert package_version("thrift") == "0.25.0"
page_oracle = Path(__file__).resolve().parents[1] / "parquet-scalar-page" / "PyArrowOracle.py"
header_fields = run_path(str(page_oracle))["header_fields"]

GROUP = 1
OPTIONAL = [b"", None, b"\xff\0\x80\1", b"x" * 48 + b"\1",
            None, None, None, None, b"\0\1", b"\xc3\xa9\1", None, b"y" * 36 + b"\1"]
REQUIRED = [b"" if row == 0 else bytes([0x81, row]) * (1 + row % 5) for row in range(12)]


def read_pairs(file, binary_name):
    group = file.read_row_group(GROUP, columns=["ordinal", binary_name], use_threads=False)
    return list(zip(group["ordinal"].to_pylist(), group[binary_name].to_pylist(), strict=True))


def page_counts(source, column, version, check_int32=False):
    assert column.compression == "UNCOMPRESSED" and not column.has_dictionary_page
    cursor = column.data_page_offset
    stop = cursor + column.total_compressed_size
    counts = []
    integers = []
    while cursor < stop:
        buffer = TMemoryBuffer(source[cursor:stop])
        header = header_fields(TCompactProtocol(buffer), (5, 8))
        body = cursor + buffer.cstringio_buf.tell()
        end = body + header[3]
        assert cursor < body <= end <= stop and header[2] == header[3] and 4 not in header
        if version == 1:
            page = header[5]
            assert header[1] == 0 and [page[key] for key in (2, 3, 4)] == [0, 3, 3]
        else:
            page = header[8]
            assert header[1] == 3 and [page[key] for key in (3, 4, 6, 7)] == [page[1], 0, 0, False]
            if check_int32:
                assert page[2] == page[5] == 0
        counts.append(page[1])
        if check_int32:
            integers.extend(struct.unpack(f"<{page[1]}i", source[body:end]))
        cursor = end
    assert cursor == stop and sum(counts) == 12
    if check_int32:
        assert integers == list(range(12, 24))
    return counts


directory = Path(sys.argv[1])
for version in (1, 2):
    base = f"plain-byte-array-v{version}"
    path = directory / f"{base}.parquet"
    with pq.ParquetFile(path) as clean:
        assert clean.schema.column(0).physical_type == "INT32"
        assert clean.schema.column(1).physical_type == "BYTE_ARRAY"
        assert clean.schema.column(0).max_definition_level == 0
        assert clean.schema.column(1).max_definition_level == 1
        columns = clean.metadata.row_group(GROUP)
        source = path.read_bytes()
        assert page_counts(source, columns.column(0), version, check_int32=True) == [8, 4]
        assert page_counts(source, columns.column(1), version) == [4, 8]
        assert read_pairs(clean, "payload") == list(zip(range(12, 24), OPTIONAL, strict=True))
    with pq.ParquetFile(directory / f"{base}-bad-length.parquet") as damaged:
        try:
            read_pairs(damaged, "payload")
        except (OSError, pa.ArrowInvalid):
            pass
        else:
            raise AssertionError("damaged selected payload was accepted")
        assert read_pairs(damaged, "key") == list(zip(range(12, 24), REQUIRED, strict=True))
    print(f"V{version} group 1: INT32 [8, 4], BYTE_ARRAY [4, 8], exact pairs and selected/unselected controls")
