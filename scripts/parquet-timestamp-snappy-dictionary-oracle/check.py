"""Reproduce Snappy TIMESTAMP dictionaries and compare exact Arrow IPC slots."""

from hashlib import sha256
from importlib.metadata import version
import json
import os
from pathlib import Path
import platform
import runpy
import struct
import subprocess
import tempfile
import zlib

import pyarrow as pa
import pyarrow.parquet as pq
from thrift.protocol.TCompactProtocol import TCompactProtocol
from thrift.transport.TTransport import TMemoryBuffer

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
DICTIONARY = runpy.run_path(str(HERE.parent / "parquet-timestamp-dictionary-oracle/check.py"))
THRIFT = DICTIONARY["THRIFT"]
SNAPPY = pa.Codec("snappy")
MIN, MAX = DICTIONARY["MIN"], DICTIONARY["MAX"]
GROUPS = [[MIN, None, -1, MIN, MAX, -1] * 30, [0, -7, None, 0, 8, None],
          [-2, None, -4, -2, -6, None] * 30]


def raw_frames(wire, column):
    start = column.dictionary_page_offset
    memory = TMemoryBuffer(wire[start:start + column.total_compressed_size])
    protocol = TCompactProtocol(memory)
    while memory.cstringio_buf.tell() < column.total_compressed_size:
        offset = start + memory.cstringio_buf.tell()
        header = THRIFT["read_struct"](protocol)
        body_start = start + memory.cstringio_buf.tell()
        body = memory.readAll(header[3][1])
        assert body == wire[body_start:body_start + header[3][1]]
        yield offset, header, body_start, body
    assert memory.cstringio_buf.tell() == column.total_compressed_size


def hybrid(data, width, expected):
    """Read the producer's RLE and bit-packed runs independently of Lean."""
    cursor, values = 0, []
    while cursor < len(data):
        count, shift = 0, 0
        while True:
            octet = data[cursor]
            cursor += 1
            count |= (octet & 127) << shift
            if octet < 128:
                break
            shift += 7
        count, packed = count >> 1, count & 1
        assert count > 0 and len(values) < expected
        if packed:
            size = count * width
            raw = data[cursor:cursor + size]
            assert len(raw) == size
            bits = int.from_bytes(raw, "little")
            remaining = expected - len(values)
            values.extend((bits >> (i * width)) & ((1 << width) - 1)
                          for i in range(min(8 * count, remaining)))
        else:
            size = (width + 7) // 8
            raw = data[cursor:cursor + size]
            assert len(raw) == size and len(values) + count <= expected
            values.extend([int.from_bytes(raw, "little")] * count)
        cursor += size
    assert cursor == len(data) and len(values) == expected
    return values


def read_group(parquet, index):
    return DICTIONARY["read_group"](parquet, index)


def inspect(wire, page_version, checksum):
    parquet = pq.ParquetFile(pa.BufferReader(wire), page_checksum_verification=True)
    assert [read_group(parquet, i) for i in range(parquet.metadata.num_row_groups)] == GROUPS
    captures, flags = [], set()
    for group_index, rows in enumerate(GROUPS):
        column = parquet.metadata.row_group(group_index).column(1)
        assert column.physical_type == "INT64" and column.compression == "SNAPPY"
        assert column.encodings == ("PLAIN", "RLE", "RLE_DICTIONARY")
        dictionary, data = list(raw_frames(wire, column))
        for _, header, _, stored in (dictionary, data):
            assert (4 in header) == checksum
            if checksum:
                assert header[4][1] % 2**32 == zlib.crc32(stored)

        dictionary_offset, header, _, stored = dictionary
        assert dictionary_offset == column.dictionary_page_offset and header[1][1] == 2
        assert header[7][1][2][1] == 0 and header[7][1][1][1] * 8 == header[2][1]
        expanded = SNAPPY.decompress(stored, header[2][1]).to_pybytes()
        distinct = list(dict.fromkeys(value for value in rows if value is not None))
        assert list(struct.iter_unpack("<q", expanded)) == [(word,) for word in distinct]

        data_offset, header, body_start, stored = data
        assert data_offset == column.data_page_offset
        if page_version == "1.0":
            assert header[1][1] == 0
            assert [header[5][1][i][1] for i in (1, 2, 3, 4)] == [len(rows), 8, 3, 3]
            expanded = SNAPPY.decompress(stored, header[2][1]).to_pybytes()
            level_bytes, = struct.unpack_from("<I", expanded)
            levels = expanded[4:4 + level_bytes]
            references = expanded[4 + level_bytes:]
            suffix_start, flag = body_start, True
        else:
            assert header[1][1] == 3
            info = header[8][1]
            assert [info[i][1] for i in (1, 2, 3, 4, 6)] == [len(rows), rows.count(None), len(rows), 8, 0]
            flag, level_bytes = info[7][1], info[5][1]
            levels = stored[:level_bytes]
            suffix = stored[level_bytes:]
            expected = header[2][1] - level_bytes
            references = SNAPPY.decompress(suffix, expected).to_pybytes() if flag else suffix
            assert len(references) == expected
            suffix_start = body_start + level_bytes
        assert hybrid(levels, 1, len(rows)) == [int(value is not None) for value in rows]
        present = [value for value in rows if value is not None]
        assert [distinct[i] for i in hybrid(references[1:], references[0], len(present))] == present
        flags.add(flag)
        captures.append((dictionary, data, suffix_start))
        print(f"V{page_version[0]} group {group_index}: dictionary {dictionary_offset}, "
              f"data {data_offset}, stored level bytes {0 if page_version == '1.0' else level_bytes}, compressed {flag}")
    assert flags == ({True} if page_version == "1.0" else {True, False})
    return captures


def corrupt(wire, index, frame, at, checksum):
    offset, header, start, body = frame
    assert start <= at < start + len(body)
    changed = wire[:at] + bytes([wire[at] ^ 1]) + wire[at + 1:]
    reader = pq.ParquetFile(pa.BufferReader(changed), page_checksum_verification=True)
    assert [read_group(reader, i) for i in range(index)] == GROUPS[:index]
    try:
        read_group(reader, index)
    except (pa.ArrowException, OSError) as error:
        if checksum:
            assert "CRC" in str(error)
    else:
        raise AssertionError("PyArrow admitted the corrupted late page")
    evidence = [offset]
    if checksum:
        declared = header[4][1] % 2**32
        computed = zlib.crc32(changed[start:start + len(body)])
        assert declared != computed
        evidence += [declared, computed]
    return changed, evidence


def fixtures():
    produce = DICTIONARY["produce"]
    v1 = produce("ns", "UTC", "1.0", codec="SNAPPY", groups=GROUPS, checksum=True)
    v2 = produce("us", None, "2.0", codec="SNAPPY", groups=GROUPS, checksum=True)
    legacy = DICTIONARY["legacy_micros"](produce("us", "UTC", "2.0", codec="SNAPPY", groups=GROUPS))
    _, _, (dictionary, _, _) = inspect(v1, "1.0", True)
    bad_dictionary, dict_evidence = corrupt(v1, 2, dictionary, dictionary[2], True)
    _, _, (_, data, _) = inspect(v2, "2.0", True)
    bad_levels, level_evidence = corrupt(v2, 2, data, data[2], True)
    _, _, (_, data, suffix) = inspect(legacy, "2.0", False)
    bad_suffix, suffix_evidence = corrupt(legacy, 2, data, suffix, False)

    older, _ = DICTIONARY["fixtures"]()
    fallback = produce("us", None, "2.0", codec="SNAPPY", fallback=True)
    parquet = pq.ParquetFile(pa.BufferReader(fallback))
    assert read_group(parquet, 0) == list(range(24))
    frames = list(raw_frames(fallback, parquet.metadata.row_group(0).column(1)))
    assert frames[0][1][1][1] == 2
    first_plain = next((index, frame[0]) for index, frame in enumerate(frames[1:], 1)
                       if frame[1][8][1][4][1] == 0)
    return {"v1": v1, "v2": v2, "legacy": legacy, "bad_dictionary": bad_dictionary,
            "bad_levels": bad_levels, "bad_suffix": bad_suffix, "fallback": fallback,
            "uncompressed": older["v2"]}, [*dict_evidence, *level_evidence, *suffix_evidence, *first_plain]


def verify_ipc(name, parquet_wire, output, unit, zone):
    expected = pa.field("ticks", pa.timestamp(unit, zone), nullable=True)
    assert pq.ParquetFile(pa.BufferReader(parquet_wire)).schema_arrow.field(1).equals(expected)
    source = pa.BufferReader(output)
    with pa.ipc.open_stream(source) as stream:
        assert stream.schema.equals(pa.schema([expected]), check_metadata=True)
        assert [batch.column(0).cast(pa.int64()).to_pylist() for batch in stream] == GROUPS
    assert source.tell() == len(output) and output.endswith(DICTIONARY["EOS"])
    messages = list(pa.ipc.MessageReader.open_stream(output))
    assert [message.type for message in messages] == ["schema"] + ["record batch"] * len(GROUPS)
    assert all(message.metadata_version == pa.ipc.MetadataVersion.V5 for message in messages)
    print(f"{name}: exact {expected.type}, {[len(rows) for rows in GROUPS]}, IPC SHA-256 {sha256(output).hexdigest()}")


def main():
    assert platform.python_implementation() == "CPython" and platform.python_version() == "3.13.5"
    assert pa.__version__ == "26.0.1" and version("thrift") == "0.25.0"
    files, evidence = fixtures()
    hashes = {name: sha256(wire).hexdigest() for name, wire in files.items()}
    assert hashes == json.loads((HERE / "fixtures.json").read_text()), hashes
    print(f"Indexed CRC, suffix and fallback evidence {evidence}", flush=True)
    with tempfile.TemporaryDirectory(prefix="parquet-timestamp-snappy-dictionary-") as temporary:
        directory = Path(temporary)
        for name, wire in files.items():
            (directory / (name + ".parquet")).write_bytes(wire)
        subprocess.run([os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
                        "-DwarningAsError=true", "--run", str(HERE / "Emit.lean"), str(directory),
                        *map(str, evidence)], cwd=ROOT, check=True)
        assert {file.stem for file in directory.glob("*.arrows")} == {"v1", "v2", "legacy"}
        for name, unit, zone in (("v1", "ns", "UTC"), ("v2", "us", None), ("legacy", "us", "UTC")):
            verify_ipc(name, files[name], (directory / (name + ".arrows")).read_bytes(), unit, zone)


if __name__ == "__main__":
    main()
