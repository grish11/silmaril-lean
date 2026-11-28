"""Reproduce exact Snappy page headers and bodies from PyArrow 26.0.1."""

from pathlib import Path
from runpy import run_path
import zlib

import pyarrow as pa
import pyarrow.parquet as pq
from thrift.protocol.TCompactProtocol import TCompactProtocol
from thrift.transport.TTransport import TMemoryBuffer

page_oracle = run_path(
    str(Path(__file__).resolve().parents[1] / "parquet-scalar-page" / "PyArrowOracle.py")
)
header_fields = page_oracle["header_fields"]
footer_codec = page_oracle["footer_codec"]

VALUES = [12, None, -5, 12] * 128


def read_verified(data):
    return pq.read_table(
        pa.BufferReader(data), use_threads=False, page_checksum_verification=True,
    ).column(0).to_pylist()


def mutated_crc(data, offset, body, relative):
    location = offset + relative
    changed = data[:location] + bytes([data[location] ^ 1]) + data[location + 1:]
    try:
        read_verified(changed)
    except (pa.ArrowInvalid, OSError) as error:
        assert "CRC" in str(error)
    else:
        raise AssertionError(f"mutated body byte {relative} passed checksum verification")
    return zlib.crc32(changed[offset:offset + len(body)])


def emit(version, checksummed):
    sink = pa.BufferOutputStream()
    pq.write_table(
        pa.table({"v": pa.array(VALUES, type=pa.int32())}), sink, version="2.6",
        data_page_version=version, compression="SNAPPY", use_dictionary=False,
        write_page_checksum=checksummed, write_statistics=False, row_group_size=len(VALUES),
    )
    data = sink.getvalue().to_pybytes()
    assert read_verified(data) == VALUES and footer_codec(data) == 1
    parquet = pq.ParquetFile(pa.BufferReader(data))
    assert parquet.metadata.num_row_groups == 1
    column = parquet.metadata.row_group(0).column(0)
    assert not column.has_dictionary_page
    start = column.data_page_offset
    transport = TMemoryBuffer(data[start:start + column.total_compressed_size])
    header = header_fields(TCompactProtocol(transport), (5, 8))
    header_size = transport.cstringio_buf.tell()
    header_bytes = data[start:start + header_size]
    expanded_size, stored_size = header[2], header[3]
    assert header_size + stored_size == column.total_compressed_size
    assert header_size + expanded_size == column.total_uncompressed_size
    assert stored_size < expanded_size
    body = transport.readAll(stored_size)
    level_bytes = 0
    if version == "1.0":
        h = header[5]
        assert header[1] == 0 and h[1] == len(VALUES) and h[2] == 0 and h[3] == h[4] == 3
    else:
        h = header[8]
        assert header[1] == 3 and h[1] == h[3] == len(VALUES) and h[2] == VALUES.count(None)
        assert h[4] == 0 and h[6] == 0 and h[7] is True
        level_bytes = h[5]
        assert 0 < level_bytes < stored_size
    expanded = body[:level_bytes] + pa.decompress(
        body[level_bytes:], expanded_size - level_bytes, codec="snappy",
    ).to_pybytes()
    signed = header.get(4)
    actual = zlib.crc32(body)
    assert actual != zlib.crc32(header_bytes + body) and actual != zlib.crc32(expanded)
    level_mutant = value_mutant = "-"
    if checksummed:
        assert signed is not None and signed % 2**32 == actual
        if version == "2.0":
            assert actual != zlib.crc32(body[level_bytes:])
            level_mutant = f"{mutated_crc(data, start + header_size, body, 0):08x}"
            value_mutant = f"{mutated_crc(data, start + header_size, body, level_bytes):08x}"
        else:
            assert signed < 0
    else:
        assert signed is None
    print(version, expanded_size, stored_size, level_bytes, signed if checksummed else "-",
          f"{actual:08x}", level_mutant, value_mutant, header_bytes.hex(), body.hex(), sep="\t")
    return body


if __name__ == "__main__":
    assert pa.__version__ == "26.0.1"
    emit("1.0", True)
    assert emit("2.0", True) == emit("2.0", False)
