#!/usr/bin/env python3
"""Replay exact Parquet V1/V2 codec-6 files against pinned PyArrow and Thrift."""
from hashlib import sha256
from importlib.metadata import version
from pathlib import Path
from struct import iter_unpack
import json
import subprocess
from tempfile import TemporaryDirectory

import pyarrow as pa
import pyarrow.parquet as pq
from thrift.Thrift import TType
from thrift.protocol.TCompactProtocol import TCompactProtocol
from thrift.transport.TTransport import TMemoryBuffer

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
PINS = {
    "zstd-plain-v1": "97449638f05cdf52675ea600b8b2c6dd49cc0bc9683dfcf320275b5c3a4ecf01",
    "zstd-plain-v2": "19d17d497a8dc92b02f227c1ca2613c91d9861c2d58208ece92a79e2ffd47c3d",
    "zstd-plain-v2-huffman": "c7ce05794fce1c0682b7ef3501c4206084510826bdd646dfa26c5f85f036ac55",
}
ZSTD = pa.Codec("zstd")


def digest(value):
    return sha256(value).hexdigest()


def require(condition, message):
    if not condition:
        raise SystemExit(message)


def fields(protocol, visitors=None, positions=None):
    found = {}
    visitors = {} if visitors is None else visitors
    protocol.readStructBegin()
    while True:
        before = protocol.trans.cstringio_buf.tell()
        _, tag, key = protocol.readFieldBegin()
        if tag == TType.STOP:
            break
        require(key not in found, "duplicate Thrift field")
        if positions is not None:
            positions[key] = (before, protocol.trans.cstringio_buf.tell())
        if key in visitors:
            kind, visit = visitors[key]
            require(tag == kind, "incorrect Thrift field type")
            found[key] = visit(protocol)
        elif tag == TType.I32:
            found[key] = protocol.readI32()
        elif tag == TType.BOOL:
            found[key] = protocol.readBool()
        else:
            protocol.skip(tag)
        protocol.readFieldEnd()
    protocol.readStructEnd()
    return found


def structs(protocol, read):
    tag, count = protocol.readListBegin()
    require(tag == TType.STRUCT, "expected Thrift list of structs")
    out = [read(protocol) for _ in range(count)]
    protocol.readListEnd()
    return out


def numeric_codecs(data):
    def column(wire):
        return fields(wire, {3: (TType.STRUCT, fields)})[3][4]

    def group(wire):
        return fields(wire, {1: (TType.LIST, lambda p: structs(p, column))})[1]

    require(data[:4] == data[-4:] == b"PAR1", "expected plaintext file magic")
    footer = len(data) - 8 - int.from_bytes(data[-8:-4], "little")
    protocol = TCompactProtocol(TMemoryBuffer(data[footer:-8]))
    return footer, fields(protocol, {4: (TType.LIST, lambda p: structs(p, group))})[4]


def first_block(payload):
    require(payload[:4] == bytes.fromhex("28 b5 2f fd"), "expected standard Zstd frame")
    descriptor = payload[4]
    single = bool(descriptor & 0x20)
    size_flag = descriptor >> 6
    header = 5 + (not single) + (0, 1, 2, 4)[descriptor & 3] + (
        int(single) if size_flag == 0 else (0, 2, 4, 8)[size_flag])
    block = int.from_bytes(payload[header:header + 3], "little")
    kind = (block >> 1) & 3
    return {"first_block_kind": kind, "first_literal_kind": payload[header + 3] & 3 if kind == 2 else None,
            "dictionary_field_bytes": (0, 1, 2, 4)[descriptor & 3], "checksum_flag": bool(descriptor & 4)}


def verify(path, table, page_version, rows_per_page, dictionary):
    source = path.read_bytes()
    parquet = pq.ParquetFile(path, page_checksum_verification=True)
    require(parquet.read().equals(table), "native independent file readback differs")
    footer, codes = numeric_codecs(source)
    all_slots = table.to_pydict()
    result = {"file_sha256": digest(source), "bytes": len(source), "footer_offset": footer,
              "names": table.column_names, "numeric_codecs": codes,
              "pages": []}
    row_start = 0
    for g in range(parquet.metadata.num_row_groups):
        group = parquet.metadata.row_group(g)
        for c in range(group.num_columns):
            column = group.column(c)
            codec = codes[g][c]
            require(codec == dictionary[column.path_in_schema] and not column.has_dictionary_page,
                    "unexpected footer codec or dictionary page")
            require(parquet.schema.column(c).max_repetition_level == 0, "expected a flat leaf")
            max_defs = parquet.schema.column(c).max_definition_level
            cursor = column.data_page_offset
            stop = cursor + column.total_compressed_size
            require(4 <= cursor < stop <= footer, "invalid page span")
            slots_done = page_index = decoded_extent = 0
            while cursor < stop:
                transport = TMemoryBuffer(source[cursor:stop])
                positions, v2_positions = {}, {}
                header = fields(TCompactProtocol(transport), {
                    5: (TType.STRUCT, fields),
                    8: (TType.STRUCT, lambda p: fields(p, positions=v2_positions)),
                }, positions)
                start = cursor + transport.cstringio_buf.tell()
                end = start + header[3]
                require(cursor < start < end <= stop and 4 not in header, "invalid page extent or CRC")
                decoded_extent += start - cursor + header[2]
                if page_version == "1.0":
                    require(header[1] == 0 and [header[5][k] for k in (2, 3, 4)] == [0, 3, 3], "V1 PLAIN/RLE")
                    count = header[5][1]
                    flag = True
                    wire_flag = None
                    codec_offset, target = start, header[2]
                    encoded = source[codec_offset:end]
                    plain = ZSTD.decompress(encoded, target).to_pybytes() if codec == 6 else encoded
                    require(len(plain) == target, "V1 decoded extent")
                    level_bytes = (4 + int.from_bytes(plain[:4], "little")) if max_defs else 0
                    plain = plain[level_bytes:]
                else:
                    require(header[1] == 3 and header[8][4] == 0 and header[8][6] == 0, "V2 PLAIN/flat")
                    data = header[8]
                    count, level_bytes = data[1], data[5]
                    wire_flag = data.get(7)
                    flag = data.get(7, True)
                    require(data[3] == count and level_bytes <= min(header[2], header[3]), "V2 fields")
                    codec_offset, target = start + level_bytes, header[2] - level_bytes
                    encoded = source[codec_offset:end]
                    plain = ZSTD.decompress(encoded, target).to_pybytes() if codec == 6 and flag else encoded
                    require(len(plain) == target, "V2 values extent")
                require(0 < count <= rows_per_page, "unexpected row count")
                slots = all_slots[column.path_in_schema][row_start + slots_done:row_start + slots_done + count]
                physical = [value for value in slots if value is not None]
                require(len(slots) == count and list(iter_unpack("<i", plain)) == [(x,) for x in physical],
                        "decoded physical bytes differ from producer rows")
                if page_version == "2.0":
                    require(header[8][2] == count - len(physical), "V2 null count")
                detail = {"group": g, "column": c, "page": page_index, "column_codec": codec,
                          "header_offset": cursor, "body_start": start, "body_end": end,
                          "codec_start": codec_offset, "expected_codec_output": target,
                          "level_bytes": level_bytes, "wire_v2_flag": wire_flag,
                          "uncompressed": header[2], "uncompressed_at": cursor + positions[2][1],
                          "compressed": header[3], "compressed_at": cursor + positions[3][1],
                          "flag_at": cursor + v2_positions[7][0] if 7 in v2_positions else None,
                          "effective_codec": 6 if codec == 6 and flag else 0,
                          "body_sha256": digest(source[start:end]), "codec_slice_sha256": digest(encoded),
                          "slots": slots}
                if detail["effective_codec"] == 6:
                    detail.update(first_block(encoded))
                    require(detail["dictionary_field_bytes"] == 0, "unexpected dictionary field")
                result["pages"].append(detail)
                slots_done += count
                page_index += 1
                cursor = end
            require(cursor == stop and slots_done == group.num_rows and decoded_extent == column.total_uncompressed_size,
                    "column chunk totals")
        row_start += group.num_rows
    require(row_start == table.num_rows, "footer row count")
    return result


def generate(work):
    schema = pa.schema([pa.field("required_i32", pa.int32(), nullable=False),
                        pa.field("optional_i32", pa.int32()),
                        pa.field("outside_codec", pa.int32(), nullable=False)])
    total = 96
    values = [
        [-(i // 16) for i in range(total)],
        [None if i % 4 == 1 else 300 if i // 32 == 1 else
         ((i * 1640531527 + 13011) % 2**32) - 2**31 for i in range(total)],
        list(range(total)),
    ]
    mixed = pa.Table.from_arrays([pa.array(column, type=pa.int32()) for column in values], schema=schema)
    names = {"required_i32": 6, "optional_i32": 6, "outside_codec": 0}

    entropy = bytes(byte % 5 for i in range(2048) for byte in sha256(i.to_bytes(4, "little")).digest())
    huffman_values = [value for (value,) in iter_unpack("<i", entropy)]
    huffman = pa.Table.from_arrays([pa.array(huffman_values, type=pa.int32())],
                                   schema=pa.schema([pa.field("huffman_i32", pa.int32(), nullable=False)]))

    files = {}
    for label, table, page_version, rows, group, codecs in (
        ("zstd-plain-v1", mixed, "1.0", 16, 32, names),
        ("zstd-plain-v2", mixed, "2.0", 16, 32, names),
        ("zstd-plain-v2-huffman", huffman, "2.0", len(huffman_values), len(huffman_values), {"huffman_i32": 6}),
    ):
        path = work / f"{label}.parquet"
        compression = {key: "zstd" if value == 6 else "NONE" for key, value in codecs.items()}
        pq.write_table(table, path, version="2.6", data_page_version=page_version, compression=compression,
                       compression_level={key: 3 for key, value in codecs.items() if value == 6},
                       use_dictionary=False, column_encoding="PLAIN", row_group_size=group,
                       write_batch_size=rows, data_page_size=1, write_statistics=False, write_page_checksum=False)
        info = verify(path, table, page_version, rows, codecs)
        flags = sorted(set(p["effective_codec"] for p in info["pages"] if p["column_codec"] == 6))
        print(f"{label} pages={len(info['pages'])} zstd_column_effective_codecs={flags} SHA256={info['file_sha256']}")
        require(info["file_sha256"] == PINS[label], "pinned producer file differs")
        files[label] = info
    optional = [p for p in files["zstd-plain-v2"]["pages"] if p["column"] == 1]
    require({p["effective_codec"] for p in optional} == {0, 6} and all(p["level_bytes"] > 0 for p in optional),
            "expected actual V2 compressed and raw suffixes with nonempty levels")
    require(any(p.get("first_block_kind") == 2 and p.get("first_literal_kind") == 2
                for p in files["zstd-plain-v2-huffman"]["pages"]), "expected actual new-tree compressed block")
    return files


def read(work, file, requests):
    instructions = work / "requests.txt"
    instructions.write_text("".join(" ".join(map(str, request)) + "\n" for request in requests))
    observed = subprocess.check_output(
        ["lake", "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true", "--run",
         HERE / "Interop.lean", file, instructions], cwd=ROOT, text=True)
    return [json.loads(line) for line in observed.splitlines()]


def request(name, group, *, input_cap=1048576, output_cap=1048576, window=8388608, commands=43690):
    return (name, "optional" if name == "optional_i32" else "required", group,
            input_cap, output_cap, window, commands)


def page(manifest, group, column, index):
    return next(p for p in manifest["pages"] if (p["group"], p["column"], p["page"]) == (group, column, index))


def slots(manifest, group, column):
    return {"slots": [slot for p in manifest["pages"] if p["group"] == group and p["column"] == column
                      for slot in p["slots"]]}


def expect_indexed(observed, at, reason):
    indices = [at[key] for key in ("group", "column", "page", "header_offset")]
    require(observed.get("pageError") == indices and observed.get("name") == "optional_i32"
            and observed["reason"].rstrip(")").endswith("." + reason), f"wrong indexed error: {observed}")


def replace_i32(data, start, previous, replacement):
    def varint(value):
        number = 2 * value
        out = bytearray()
        while number >= 128:
            out.append((number % 128) | 128)
            number //= 128
        out.append(number)
        return bytes(out)
    old, new = varint(previous), varint(replacement)
    require(len(old) == len(new) and data[start:start + len(old)] == old, "not a same-width i32 control")
    data[start:start + len(old)] = new


def mutations(work, manifest, *, v1):
    stem = "zstd-plain-v1" if v1 else "zstd-plain-v2"
    source = (work / f"{stem}.parquet").read_bytes()
    target = page(manifest, 1, 1, 1)
    require(target["effective_codec"] == 6, "expected selected compressed page")
    corrupted = bytearray(source)
    corrupted[target["codec_start"]] ^= 1
    file = work / f"{stem}-bad-magic.parquet"
    file.write_bytes(corrupted)
    observed = read(work, file, [request("optional_i32", group) for group in range(3)])
    require(observed[0] == slots(manifest, 0, 1) and observed[2] == slots(manifest, 2, 1),
            "damage affected another row group")
    expect_indexed(observed[1], target, "badMagic")
    print(f"{stem} malformed frame: group 1 column 1 page 1 header {target['header_offset']}; groups 0 and 2 match")
    if v1:
        return

    def checked_mutation(name, change, expected, at=target):
        data = bytearray(source)
        change(data)
        mutated = work / f"{name}.parquet"
        mutated.write_bytes(data)
        [observed] = read(work, mutated, [request("optional_i32", at["group"])])
        if expected == "invalidV2Lengths":
            require(observed.get("columnError") == [at["group"], at["column"]]
                    and observed.get("name") == "optional_i32" and ".framing" in observed["reason"]
                    and observed["reason"].rstrip(")").endswith(".invalidV2Lengths"),
                    f"wrong checked-header rejection: {observed}")
        elif isinstance(expected, str):
            expect_indexed(observed, at, expected)
        else:
            require(observed == expected, f"{name}: output changed")
        print(f"{name}: {expected if isinstance(expected, str) else 'matches with absent flag'}")

    def output_size(n):
        return lambda data: replace_i32(data, target["uncompressed_at"], target["uncompressed"], n)

    checked_mutation("wrong-regenerated-size", output_size(target["uncompressed"] + 1), "outputSizeMismatch")
    checked_mutation("levels-over-declared-output", output_size(target["level_bytes"] - 1), "invalidV2Lengths")
    checked_mutation("levels-over-declared-input", lambda data: replace_i32(
        data, target["compressed_at"], target["compressed"], target["level_bytes"] - 1), "invalidV2Lengths")

    def set_flag(data, at, new):
        where = at["flag_at"]
        require(data[where] & 15 == (1 if at["wire_v2_flag"] else 2), "wrong Compact bool field")
        data[where] = new

    checked_mutation("false-flag-on-zstd", lambda data: set_flag(data, target, 0x12), "invalidV2Lengths")
    checked_mutation("missing-flag", lambda data: set_flag(data, target, 0x91), slots(manifest, 1, 1))
    raw = next(p for p in manifest["pages"] if p["column"] == 1 and p["wire_v2_flag"] is False)
    checked_mutation("true-flag-on-raw", lambda data: set_flag(data, raw, 0x11), "badMagic", at=raw)

    declared = bytearray(source)
    replace_i32(declared, target["compressed_at"], target["compressed"], target["compressed"] - 1)
    length_error = work / "wrong-physical-length.parquet"
    length_error.write_bytes(declared)
    [observed] = read(work, length_error, [request("optional_i32", 1)])
    require(observed.get("columnError") == [1, 1] and ".framing" in observed["reason"],
            f"incorrect physical-length admission: {observed}")
    print("wrong physical length: checked chunk framing rejected the residual byte")


def main():
    require(pa.__version__ == "26.0.1" and version("thrift") == "0.25.0", "wrong producer versions")
    with TemporaryDirectory(prefix="silmaril-parquet-zstd-") as directory:
        work = Path(directory)
        fixtures = generate(work)
        for name, manifest in fixtures.items():
            file = work / f"{name}.parquet"
            queries, expected = [], []
            for g, codecs in enumerate(manifest["numeric_codecs"]):
                for c, codec in enumerate(codecs):
                    column = manifest["names"][c]
                    queries.append(request(column, g))
                    expected.append(slots(manifest, g, c) if codec == 6 else None)
            observed = read(work, file, queries)
            for (query, actual, wanted) in zip(queries, observed, expected, strict=True):
                if wanted is not None:
                    require(actual == wanted, f"{name}: wrong selected slots for {query[:3]}")
                else:
                    require(actual.get("columnError") == [query[2], 2] and actual["reason"].endswith(".codec 0"),
                            f"codec-6 admission accepted codec 0: {actual}")
            count = sum(len(item["slots"]) for item in expected if item is not None)
            print(f"{name}: {count} exact selected slots; codec-0 columns rejected")

        v2 = fixtures["zstd-plain-v2"]
        v2_file = work / "zstd-plain-v2.parquet"
        first = page(v2, 1, 1, 0)
        observed = read(work, v2_file, [
            request("optional_i32", 1, input_cap=0), request("optional_i32", 1, output_cap=0),
            request("optional_i32", 1, window=0),
        ])
        for actual, error in zip(observed, ("compressedLimit", "outputLimit", "windowLimit"), strict=True):
            expect_indexed(actual, first, error)
        [commands] = read(work, work / "zstd-plain-v2-huffman.parquet",
                          [request("huffman_i32", 0, commands=0)])
        huffman = page(fixtures["zstd-plain-v2-huffman"], 0, 0, 0)
        require(commands.get("pageError") == [0, 0, 0, huffman["header_offset"]]
                and commands["reason"].rstrip(")").endswith(".sequenceLimit"), f"wrong command cap: {commands}")
        print("input, output, window and command bounds: indexed rejection")
        mutations(work, fixtures["zstd-plain-v1"], v1=True)
        mutations(work, v2, v1=False)


if __name__ == "__main__":
    main()
