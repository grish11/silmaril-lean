"""Reproduce full-file FLOAT BYTE_STREAM_SPLIT fixtures and check their bit lanes."""

import argparse
from hashlib import sha256
from pathlib import Path
from runpy import run_path
import struct

import pyarrow as pa
import pyarrow.parquet as pq
from thrift.Thrift import TType
from thrift.protocol.TCompactProtocol import TCompactProtocol
from thrift.transport.TTransport import TMemoryBuffer

ROOT = Path(__file__).resolve().parents[2]
header_fields = run_path(str(ROOT / "scripts/parquet-flat-page/PyArrowOracle.py"))["header_fields"]
footer_helpers = run_path(str(ROOT / "scripts/parquet-payload-oracle/check.py"))
fields, one_struct = (footer_helpers[key] for key in ("fields", "one_struct"))
slots = [
    0, None, 0x80000000, 0x7FC12345, 1, 0xFFC54321, 0x7F800000, None,
    0xFF800000, 0x3F800000, None, 0x80000001, 0x00800000, None, 0x7F7FFFFF, 0x80400000,
    0xBF800000, 0x3F000001, None, 0x7FC10001, None, None, None, None,
]
bitmap = sum((slot is not None) << index for index, slot in enumerate(slots)).to_bytes(3, "little")
physical = b"".join(struct.pack("<I", slot or 0) for slot in slots)
schema = pa.schema([pa.field("measurement", pa.float32(), nullable=True)])
column = pa.Array.from_buffers(pa.float32(), len(slots), [pa.py_buffer(bitmap), pa.py_buffer(physical)])
table = pa.Table.from_arrays([column], schema=schema)


def footer_codecs(source, footer):
    transport = TMemoryBuffer(source[footer:-8])

    def offset_and_codec(reader):
        offset = footer + transport.cstringio_buf.tell()
        return offset, reader.readI32()

    def metadata(reader):
        return fields(reader, {4: (TType.I32, offset_and_codec)})[4]

    def chunk(reader):
        return fields(reader, {3: (TType.STRUCT, metadata)})[3]

    def group(reader):
        return fields(reader, {1: (TType.LIST, lambda p: one_struct(p, chunk))})[1]

    def groups(reader):
        tag, count = reader.readListBegin()
        assert tag == TType.STRUCT and count == 3
        result = [group(reader) for _ in range(count)]
        reader.readListEnd()
        return result

    return fields(TCompactProtocol(transport), {4: (TType.LIST, groups)})[4]


def verify(path, version):
    raw = path.read_bytes()
    file = pq.ParquetFile(path)
    assert file.metadata.num_row_groups == 3
    leaf = file.schema.column(0)
    assert leaf.physical_type == "FLOAT" and leaf.max_definition_level == 1 and leaf.max_repetition_level == 0
    footer = len(raw) - 8 - int.from_bytes(raw[-8:-4], "little")
    print(path.name, len(raw), sha256(raw).hexdigest(), "footer", footer)
    for group_index in range(3):
        group_start = 8 * group_index
        readback = file.read_row_group(group_index, use_threads=False).column(0).chunk(0)
        assert readback.view(pa.uint32()).to_pylist() == slots[group_start:group_start + 8]
        metadata = file.metadata.row_group(group_index).column(0)
        assert metadata.compression == "UNCOMPRESSED" and not metadata.has_dictionary_page
        cursor = metadata.data_page_offset
        stop = cursor + metadata.total_compressed_size
        assert 4 <= cursor < stop <= footer
        for page_index in range(2):
            reader = TMemoryBuffer(raw[cursor:stop])
            header = header_fields(TCompactProtocol(reader), (5, 8))
            start = cursor + reader.cstringio_buf.tell()
            end = start + header[3]
            assert cursor < start <= end <= stop and header[2] == header[3] and 4 not in header
            body = raw[start:end]
            page_start = group_start + 4 * page_index
            logical = slots[page_start:page_start + 4]
            words = [struct.pack("<I", slot) for slot in logical if slot is not None]
            if version == "1.0":
                assert header[1] == 0 and [header[5][k] for k in (1, 2, 3, 4)] == [4, 9, 3, 3]
                length = 4 + struct.unpack_from("<I", body)[0]
            else:
                assert header[1] == 3
                assert [header[8][k] for k in (1, 2, 3, 4, 6)] == [4, 4 - len(words), 4, 9, 0]
                length = header[8][5]
            assert length <= len(body)
            lanes = body[length:]
            assert lanes == bytes(word[lane] for lane in range(4) for word in words)
            print(group_index, page_index, "header", cursor, "body", start, end,
                  "lanes", lanes.hex() or "-", "present", len(words))
            cursor = end
        assert cursor == stop
    codecs = footer_codecs(raw, footer)
    assert all(codec == 0 for _, codec in codecs)
    if version == "2.0":
        offset, _ = codecs[0]
        assert offset == 285 and raw[offset] == 0
        patched = bytearray(raw)
        patched[offset] = 2
        assert footer_codecs(patched, footer)[0] == (offset, 1)
        print("first-group codec field", offset, "changes from 0 to 1 under the one-byte control")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("directory", type=Path)
    args = parser.parse_args()
    assert pa.__version__ == "26.0.1"
    args.directory.mkdir(parents=True, exist_ok=True)
    for version in ("1.0", "2.0"):
        path = args.directory / f"float-bss-v{version[0]}.parquet"
        pq.write_table(
            table, path, version="2.6", data_page_version=version, compression="NONE",
            use_dictionary=False, use_byte_stream_split=True, write_statistics=False,
            write_page_checksum=False, row_group_size=8, write_batch_size=4, data_page_size=1,
        )
        verify(path, version)


if __name__ == "__main__":
    main()
