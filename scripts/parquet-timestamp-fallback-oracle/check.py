"""Compare exact Parquet fallback frames, ticks and the actual native Arrow IPC."""

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

import pyarrow as pa
import pyarrow.parquet as pq
from thrift.Thrift import TType

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
DICTIONARY = runpy.run_path(str(HERE.parent / "parquet-timestamp-dictionary-oracle/check.py"))
THRIFT = DICTIONARY["THRIFT"]
MIN, MAX = DICTIONARY["MIN"], DICTIONARY["MAX"]
MULTI = [
    [MIN, None, -11, MAX] + [None if i % 5 == 2 else -100 + i for i in range(20)],
    [-17, MAX, None, MIN] + [None if i % 5 == 3 else 200 + i for i in range(20)],
]


def read_group(parquet, index):
    return DICTIONARY["read_group"](parquet, index)


def inspect(wire, version, rows, zone):
    parquet = pq.ParquetFile(pa.BufferReader(wire))
    expected_field = pa.field("ticks", pa.timestamp("us", zone), nullable=True)
    assert parquet.schema.column(0).physical_type == "INT32"
    assert parquet.schema.column(1).physical_type == "INT64"
    assert parquet.schema_arrow.field(1).equals(expected_field)
    assert [read_group(parquet, i) for i in range(parquet.metadata.num_row_groups)] == rows
    original = []
    for group_index, expected in enumerate(rows):
        column = parquet.metadata.row_group(group_index).column(1)
        assert column.compression == "UNCOMPRESSED" and column.num_values == len(expected)
        dictionary, *pages = DICTIONARY["frames"](wire, column)
        offset, header, _, payload = dictionary
        assert offset == column.dictionary_page_offset and header[1][1] == 2
        assert header[7][1][2] == (TType.I32, 0)
        entries = [word for word, in struct.iter_unpack("<q", payload)]
        assert len(entries) == header[7][1][1][1]
        assert pages[0][0] == column.data_page_offset
        cursor, encodings = 0, []
        for _, header, _, payload in pages:
            assert header[1][1] == (0 if version == 1 else 3)
            info = header[5 if version == 1 else 8][1]
            count = info[1][1]
            assert count == 4
            slots = expected[cursor:cursor + count]
            cursor += count
            present = [value for value in slots if value is not None]
            if version == 1:
                assert [info[i][1] for i in (3, 4)] == [3, 3]
                level_start, level_stop = 4, 4 + struct.unpack_from("<I", payload)[0]
                encoding = info[2][1]
            else:
                assert [info[i][1] for i in (2, 3, 6, 7)] == [slots.count(None), count, 0, False]
                level_start, level_stop = 0, info[5][1]
                encoding = info[4][1]
            levels = payload[level_start:level_stop]
            if len(present) == count:
                assert levels == b"\x08\x01"
            else:
                assert len(levels) == 2 and levels[0] == 3
                assert [(levels[1] >> i) & 1 for i in range(count)] == [v is not None for v in slots]
            values = payload[level_stop:]
            encodings.append(encoding)
            if encoding == 8:
                assert entries == list(dict.fromkeys(present))
                assert len(values) == 4 and values[:2] == b"\x02\x03"
                packed = int.from_bytes(values[2:], "little")
                assert [entries[(packed >> (2 * i)) & 3] for i in range(len(present))] == present
            else:
                assert encoding == 0
                assert list(struct.iter_unpack("<q", values)) == [(value,) for value in present]
        assert cursor == len(expected) and encodings == [8] + [0] * 5
        print(f"V{version} group {group_index}: dictionary {offset}, data offsets {[p[0] for p in pages]}, "
              f"data encodings {encodings}")
        original.append(pages)
    return original


def truncate_last_plain(wire, last):
    offset, header, start, payload = last
    assert header[8][1][4][1] == 0
    end = start + len(payload)
    footer_size, = struct.unpack_from("<I", wire, len(wire) - 8)
    assert end == len(wire) - 8 - footer_size
    for field in (2, 3):
        header[field] = (TType.I32, len(payload) - 1)
    changed_header = THRIFT["encode"](header)
    assert len(changed_header) == start - offset
    changed = wire[:offset] + changed_header + payload[:-1] + wire[end:]

    def shrink(metadata):
        group = THRIFT["list_field"](metadata, 4)[1]
        column = THRIFT["column_metadata"](metadata, group=1, column=1)
        for fields, keys in ((group, (2, 6)), (column, (6, 7))):
            for key in keys:
                kind, size = fields[key]
                fields[key] = kind, size - 1

    broken = THRIFT["rewrite_footer"](changed, shrink)
    parquet = pq.ParquetFile(pa.BufferReader(broken))
    assert read_group(parquet, 0) == MULTI[0]
    try:
        read_group(parquet, 1)
    except (pa.ArrowException, OSError):
        pass
    else:
        raise AssertionError("PyArrow admitted the truncated PLAIN payload")
    return broken


def change_tag(wire, frame, tag):
    offset, header, start, _ = frame
    header[8][1][4] = TType.I32, tag
    changed = THRIFT["encode"](header)
    assert len(changed) == start - offset
    return wire[:offset] + changed + wire[start:]


def fixtures():
    predecessor, offsets = DICTIONARY["fixtures"]()
    original = predecessor["fallback"]
    predecessor_pins = json.loads((HERE.parent / "parquet-timestamp-dictionary-oracle/fixtures.json").read_text())
    assert sha256(original).hexdigest() == predecessor_pins["fallback"]
    one = [list(range(24))]
    one_pages = inspect(original, 2, one, None)[0]
    v1 = DICTIONARY["produce"]("us", "UTC", "1.0", fallback=True, groups=MULTI)
    inspect(v1, 1, MULTI, "UTC")
    v2 = DICTIONARY["produce"]("us", "UTC", "2.0", fallback=True, groups=MULTI)
    v2_pages = inspect(v2, 2, MULTI, "UTC")
    bad = truncate_last_plain(v2, v2_pages[1][-1])
    first_plain = change_tag(original, one_pages[0], 0)
    reentry = change_tag(original, one_pages[2], 8)
    return {
        "existing": original, "v1": v1, "v2": v2, "bad": bad, "plain_first": first_plain,
        "reentry": reentry, "dictionary_only": predecessor["v2"], "compressed": predecessor["snappy"],
    }, [*offsets[1:], one_pages[0][0], one_pages[2][0], v2_pages[1][-1][0]]


def check_ipc(output, expected, zone):
    field = pa.field("ticks", pa.timestamp("us", zone), nullable=True)
    source = pa.BufferReader(output)
    with pa.ipc.open_stream(source) as stream:
        assert stream.schema.equals(pa.schema([field]), check_metadata=True)
        assert [batch.column(0).cast(pa.int64()).to_pylist() for batch in stream] == expected
    assert source.tell() == len(output) and output.endswith(DICTIONARY["EOS"])
    messages = list(pa.ipc.MessageReader.open_stream(output))
    assert [message.type for message in messages] == ["schema"] + ["record batch"] * len(expected)
    assert all(message.metadata_version == pa.ipc.MetadataVersion.V5 for message in messages)


def main():
    assert platform.python_implementation() == "CPython" and platform.python_version() == "3.13.5"
    assert pa.__version__ == "26.0.1" and version("thrift") == "0.25.0"
    files, offsets = fixtures()
    hashes = {name: sha256(wire).hexdigest() for name, wire in files.items()}
    assert hashes == json.loads((HERE / "fixtures.json").read_text()), hashes
    with tempfile.TemporaryDirectory(prefix="parquet-timestamp-fallback-") as temporary:
        directory = Path(temporary)
        for name, wire in files.items():
            (directory / (name + ".parquet")).write_bytes(wire)
        subprocess.run([os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
                        "-DwarningAsError=true", "--run", str(HERE / "Emit.lean"), str(directory),
                        *map(str, offsets)], cwd=ROOT, check=True)
        assert {file.stem for file in directory.glob("*.arrows")} == {"existing", "v1", "v2"}
        for name, rows, zone in (("existing", [list(range(24))], None), ("v1", MULTI, "UTC"), ("v2", MULTI, "UTC")):
            output = (directory / (name + ".arrows")).read_bytes()
            check_ipc(output, rows, zone)
            print(f"{name}: exact V5 IPC {list(map(len, rows))}, SHA-256 {sha256(output).hexdigest()}")


if __name__ == "__main__":
    main()
