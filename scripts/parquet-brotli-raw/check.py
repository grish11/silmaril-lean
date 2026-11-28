#!/usr/bin/env python3
"""Replay independent codec-4 pages and authored V2 raw-Brotli controls."""
import argparse
from hashlib import sha256
from importlib.metadata import version
from pathlib import Path
from struct import iter_unpack, pack
import json
import subprocess
from tempfile import TemporaryDirectory

import pyarrow as pa
import pyarrow.parquet as pq
from thrift.Thrift import TType
from thrift.protocol.TCompactProtocol import TCompactProtocol
from thrift.transport.TTransport import TMemoryBuffer

PIN = "028fb5a23661f123017c060daa546b55cf4bde29"
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]


def check(condition, message):
    if not condition:
        raise ValueError(message)


def digest(data):
    return sha256(data).hexdigest()


def run(*args, data=None):
    return subprocess.check_output(args, input=data)


def fields(wire, nested=None):
    result, locations = {}, {}
    nested = nested or {}
    wire.readStructBegin()
    while True:
        field_position = wire.trans.cstringio_buf.tell()
        _, kind, number = wire.readFieldBegin()
        if kind == TType.STOP:
            break
        check(number not in result, "duplicate field")
        locations[number] = (field_position, wire.trans.cstringio_buf.tell())
        if number in nested:
            result[number] = nested[number](wire)
        elif kind == TType.I32:
            result[number] = wire.readI32()
        elif kind == TType.I64:
            result[number] = wire.readI64()
        elif kind == TType.BOOL:
            result[number] = wire.readBool()
        else:
            wire.skip(kind)
        wire.readFieldEnd()
    wire.readStructEnd()
    return result, locations


def one_list(wire, read):
    kind, count = wire.readListBegin()
    check(kind == TType.STRUCT and count == 1, "expected one struct")
    value = read(wire)
    wire.readListEnd()
    return value


def inspect(data, parquet):
    check(data[:4] == data[-4:] == b"PAR1", "file magic")
    footer_at = len(data) - 8 - int.from_bytes(data[-8:-4], "little")
    footer_wire = TCompactProtocol(TMemoryBuffer(data[footer_at:-8]))

    def chunk(w):
        return fields(w, {3: fields})

    def group(w):
        return fields(w, {1: lambda xs: one_list(xs, chunk)})

    footer, _ = fields(footer_wire, {4: lambda xs: one_list(xs, group)})
    row_group, rg_places = footer[4]
    column, _ = row_group[1]
    metadata, col_places = column[3]
    check(metadata[4] == 4 and 10 not in metadata and 11 not in metadata, "codec-4 nondictionary chunk")
    check(not parquet.metadata.row_group(0).column(0).has_column_index, "no column index")
    check(not parquet.metadata.row_group(0).column(0).has_offset_index, "no offset index")
    start = metadata[9]
    reader = TCompactProtocol(TMemoryBuffer(data[start:footer_at]))
    page, page_places = fields(reader, {5: fields, 8: fields})
    body_at = start + reader.trans.cstringio_buf.tell()
    check(start == 4 and body_at + page[3] == start + metadata[7] == footer_at, "one exact page")
    check(body_at - start + page[2] == metadata[6], "uncompressed chunk size")
    check(4 not in page, "no page CRC")
    if page[1] == 3:
        v2, v2_places = page[8]
        check(v2[6] == 0 and v2[4] == 0 and v2[1] == v2[3], "optional flat PLAIN V2")
        prefix, flag = v2[5], v2.get(7, True)
        check(0 < prefix <= min(page[2], page[3]), "bounded raw level extent")
        flag_at = start + v2_places[7][0] if 7 in v2_places else None
    else:
        v1, _ = page[5]
        check(page[1] == 0 and [v1[k] for k in (2, 3, 4)] == [0, 3, 3], "optional flat PLAIN V1")
        prefix, flag, flag_at = 0, True, None
    return {"header_at": start, "body_at": body_at, "footer_at": footer_at, "type": page[1],
            "body_bytes": page[3], "expanded_bytes": page[2], "raw_prefix": prefix, "flag": flag,
            "flag_at": flag_at, "page_compressed_at": start + page_places[3][1],
            "chunk_compressed_at": col_places[7][1], "chunk_bytes": metadata[7],
            "group_compressed_at": rg_places[6][1] if 6 in rg_places else None,
            "group_compressed": row_group.get(6)}


def replace_positive_varint(data, at, old, new):
    def zigzag(value):
        value *= 2
        result = bytearray()
        while value >= 128:
            result.append((value % 128) | 128)
            value //= 128
        result.append(value)
        return bytes(result)
    before, after = zigzag(old), zigzag(new)
    check(len(before) == len(after) and data[at:at + len(before)] == before, "same-width patch")
    data[at:at + len(before)] = after


def author_v2(data, layout, suffix, explicit=True):
    check(layout["type"] == 3 and layout["flag"] is False, "source is actual raw V2")
    body_at, footer_at = layout["body_at"], layout["footer_at"]
    values_at = body_at + layout["raw_prefix"]
    delta = len(suffix) - (footer_at - values_at)
    prefix = bytearray(data[:values_at])
    footer = bytearray(data[footer_at:])
    flag_at = layout["flag_at"]
    check(prefix[flag_at] == 0x12, "expected compact false field after preceding bool delta")
    prefix[flag_at] = 0x11 if explicit else 0x91
    replace_positive_varint(prefix, layout["page_compressed_at"], layout["body_bytes"], layout["body_bytes"] + delta)
    replace_positive_varint(footer, layout["chunk_compressed_at"], layout["chunk_bytes"], layout["chunk_bytes"] + delta)
    if layout["group_compressed_at"] is not None:
        replace_positive_varint(footer, layout["group_compressed_at"], layout["group_compressed"],
                                layout["group_compressed"] + delta)
    return bytes(prefix) + suffix + bytes(footer)


def build_reference(source, work):
    if source is None:
        source = work / "brotli"
        run("git", "init", "-q", source)
        run("git", "-C", source, "fetch", "-q", "--depth=1", "https://github.com/google/brotli.git", PIN)
        run("git", "-C", source, "checkout", "-q", "--detach", "FETCH_HEAD")
    check(run("git", "-C", source, "rev-parse", "HEAD").decode().strip() == PIN, "libbrotli pin")
    check(run("git", "-C", source, "diff", "HEAD", "--") == b"", "unmodified reference")
    build = work / "build"
    run("cmake", "-S", source, "-B", build, "-DCMAKE_BUILD_TYPE=Release", "-DBUILD_TESTING=OFF")
    run("cmake", "--build", build, "--target", "brotli", "--parallel", "4")
    cli = build / "brotli"
    check(run(cli, "--version").strip() == b"brotli 1.2.0", "native version")
    return cli


def make_cases(cli, work):
    raw = b"".join(sha256(i.to_bytes(4, "little")).digest() for i in range(128))
    integers = [n for (n,) in iter_unpack("<i", raw)]
    varied = [None if i % 8 == 1 else n for i, n in enumerate(integers)]
    repeated = [None if i % 8 == 1 else 300 for i in range(len(varied))]
    cases = {}
    for name, page_version, level, rows, nullable, control in (
        ("producer-v1-raw-brotli", "1.0", 0, integers, False, "v1"),
        ("producer-v1-entropy-brotli", "1.0", 0, varied, True, "entropy"),
        ("producer-v2-uncompressed-suffix", "2.0", 0, varied, True, "raw"),
        ("producer-v2-entropy-brotli", "2.0", 5, repeated, True, "entropy"),
    ):
        schema = pa.schema([pa.field("x", pa.int32(), nullable=nullable)])
        table = pa.Table.from_arrays([pa.array(rows, type=pa.int32())], schema=schema)
        path = work / f"{name}.parquet"
        pq.write_table(table, path, compression="brotli", compression_level=level, version="2.6",
                       data_page_version=page_version, use_dictionary=False, column_encoding="PLAIN",
                       write_statistics=False, write_page_checksum=False, row_group_size=len(rows))
        cases[name] = (path.read_bytes(), rows, "PyArrow", control)

    raw_seed = cases["producer-v2-uncompressed-suffix"][0]
    raw_layout = inspect(raw_seed, pq.ParquetFile(pa.BufferReader(raw_seed)))
    values_at = raw_layout["body_at"] + raw_layout["raw_prefix"]
    raw_values = raw_seed[values_at:raw_layout["footer_at"]]
    raw_brotli = run(cli, "--stdout", "-q", "0", "-w", "16", data=raw_values)
    for name, explicit, control in (("authored-v2-raw-brotli", True, "v2"),
                                    ("authored-v2-absent-flag", False, "accept")):
        cases[name] = (author_v2(raw_seed, raw_layout, raw_brotli, explicit), varied,
                       "authored wrapper, PyArrow levels, libbrotli values", control)
    # WBITS=16, an empty metadata block, then an aligned raw block and EOS.
    raw_header_word = ((len(raw_values) - 1) << 3) | (1 << 19)
    metadata_stream = b"\x0c" + raw_header_word.to_bytes(3, "little") + raw_values + b"\x03"
    cases["authored-v2-metadata"] = (author_v2(raw_seed, raw_layout, metadata_stream), varied,
                                     "authored metadata and raw meta-block control", "metadata")
    return cases


def replay(cli, work):
    summary = {"libbrotli_commit": PIN, "pyarrow": pa.__version__, "thrift": version("thrift"), "files": {}}
    outcomes = {
        "v1": ["wrong-codec", "declared-input", "declared-output-small", "declared-output-large",
               "input-cap", "output-cap", "window-cap", "step-cap", "truncated", "trailing", "default-codec-4"],
        "v2": ["levels-over-input", "levels-over-output", "false-flag-on-compressed"],
        "raw": ["levels-over-input", "levels-over-output", "true-flag-on-raw"],
        "accept": [],
        "entropy": ["unsupportedCompressed"],
        "metadata": ["unsupportedMetadata"],
    }
    for name, (data, slots, provenance, control) in make_cases(cli, work).items():
        path = work / f"{name}.parquet"
        path.write_bytes(data)
        parquet = pq.ParquetFile(pa.BufferReader(data))
        check(parquet.read().column("x").to_pylist() == slots, name + " native file readback")
        layout = inspect(data, parquet)
        start, prefix, stop = layout["body_at"], layout["raw_prefix"], layout["footer_at"]
        encoded = data[start + prefix:stop]
        decoded = run(cli, "--decompress", "--stdout", data=encoded) if layout["flag"] else encoded
        plain = data[start:start + prefix] + decoded
        check(len(plain) == layout["expanded_bytes"], name + " exact native plain extent")
        physical = [n for n in slots if n is not None]
        check(decoded.endswith(pack("<" + "i" * len(physical), *physical)), name + " physical bytes")
        expected = work / "expanded.body"
        expected.write_bytes(plain)
        result = subprocess.run(
            ["lake", "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true", "--run",
             HERE / "Interop.lean", path, expected, control], cwd=ROOT, capture_output=True, text=True)
        check(result.returncode == 0 and not result.stderr, result.stdout + result.stderr)
        label = "match"
        expected_lines = outcomes[control]
        if control in ("entropy", "metadata"):
            label = expected_lines[0]
        else:
            expected_lines = [f"{start} {stop} {len(plain)}", *expected_lines]
        check(result.stdout.splitlines() == expected_lines, f"{name}: {result.stdout}")
        summary["files"][name] = {"provenance": provenance, "file_sha256": digest(data),
                                 "file_bytes": len(data), "wire_sha256": digest(encoded),
                                 "expanded_body_sha256": digest(plain), "body_offset": start,
                                 "body_bytes": stop - start, "expanded_bytes": len(plain),
                                 "page_type": layout["type"], "raw_prefix": prefix,
                                 "flag": layout["flag"] if layout["flag_at"] is not None else None,
                                 "result": label, "controls": outcomes[control]}
        print(f"{name}: {label}, body [{start}, {stop}), raw prefix {prefix}, "
              f"expanded size {len(plain)}, SHA-256 {digest(data)}")
        for checked in outcomes[control]:
            print(f"  {checked}")
    return summary


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--brotli-source", type=Path)
    args = parser.parse_args()
    check((pa.__version__, version("thrift")) == ("26.0.1", "0.25.0"), "producer version pins")
    with TemporaryDirectory(prefix="silmaril-parquet-brotli-raw-") as path:
        work = Path(path)
        source = args.brotli_source.resolve() if args.brotli_source else None
        cli = build_reference(source, work)
        print(f"libbrotli v1.2.0 {PIN}, PyArrow {pa.__version__}, Thrift {version('thrift')}")
        check(replay(cli, work) == json.loads((HERE / "fixtures.json").read_text()), "pinned fixtures differ")


if __name__ == "__main__":
    main()
