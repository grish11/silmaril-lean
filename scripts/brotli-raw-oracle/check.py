#!/usr/bin/env python3
"""Compare the strict raw Brotli profile with pinned libbrotli and PyArrow."""
import argparse
from hashlib import sha256
from importlib.metadata import version
import json
from pathlib import Path
from struct import iter_unpack
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


def digest(data):
    return sha256(data).hexdigest()


def require(condition, message):
    if not condition:
        raise SystemExit(message)


def run(*command, data=None):
    return subprocess.check_output(command, input=data)


def fields(protocol, wanted):
    out = {}
    protocol.readStructBegin()
    while True:
        _, tag, number = protocol.readFieldBegin()
        if tag == TType.STOP:
            break
        if number in wanted:
            expected, reader = wanted[number]
            require(tag == expected and number not in out, "unexpected Thrift field")
            out[number] = reader(protocol)
        else:
            protocol.skip(tag)
        protocol.readFieldEnd()
    protocol.readStructEnd()
    require(out.keys() == wanted.keys(), "missing Thrift field")
    return out


def one_list(p, read):
    tag, count = p.readListBegin()
    require(tag == TType.STRUCT and count == 1, "expected one Thrift struct")
    out = read(p)
    p.readListEnd()
    return out


def parquet_payload(work, raw):
    require(pa.__version__ == "26.0.1", "PyArrow pin")
    path = work / "brotli-v1.parquet"
    values = [value for (value,) in iter_unpack("<i", raw)]
    table = pa.Table.from_arrays([pa.array(values, type=pa.int32())],
                                 schema=pa.schema([pa.field("x", pa.int32(), nullable=False)]))
    pq.write_table(table, path, compression="brotli", compression_level=0, version="2.6",
                   data_page_version="1.0", use_dictionary=False, column_encoding="PLAIN",
                   write_statistics=False, write_page_checksum=False, row_group_size=len(values))
    reader = pq.ParquetFile(path)
    require(reader.read().equals(table), "independent Parquet readback")
    field_i32 = (TType.I32, TCompactProtocol.readI32)

    def column(p):
        return fields(p, {3: (TType.STRUCT, lambda c: fields(c, {4: field_i32}))})[3][4]

    def group(p):
        return fields(p, {1: (TType.LIST, lambda xs: one_list(xs, column))})[1]

    file = path.read_bytes()
    require(file[:4] == file[-4:] == b"PAR1", "Parquet magic")
    footer = len(file) - 8 - int.from_bytes(file[-8:-4], "little")
    protocol = TCompactProtocol(TMemoryBuffer(file[footer:-8]))
    codec = fields(protocol, {4: (TType.LIST, lambda xs: one_list(xs, group))})[4]
    require(codec == 4, "numeric Brotli codec ID")
    chunk = reader.metadata.row_group(0).column(0)
    start = chunk.data_page_offset
    transport = TMemoryBuffer(file[start:start + chunk.total_compressed_size])
    header = fields(TCompactProtocol(transport), {1: field_i32, 2: field_i32, 3: field_i32})
    require(header[1] == 0 and header[2] == len(raw), "exact V1 page type and regenerated size")
    offset = start + transport.cstringio_buf.tell()
    end = offset + header[3]
    require(end == start + chunk.total_compressed_size <= footer, "exact single page span")
    return file[offset:end], {"sha256": digest(file), "bytes": len(file), "codec": codec, "body_offset": offset}


def raw_stream(plain, window_code, window_width, nibbles):
    """Author one raw meta-block for the RFC length transitions."""
    stored = len(plain) - 1
    header = window_code | ((nibbles - 4) << (window_width + 1))
    header |= stored << (window_width + 3)
    raw_bit = window_width + 3 + 4 * nibbles
    header |= 1 << raw_bit
    return header.to_bytes((raw_bit + 8) // 8, "little") + plain + b"\x03"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--brotli-source", type=Path, help="optional checkout at the pinned SHA")
    args = parser.parse_args()
    require(pa.__version__ == "26.0.1" and version("thrift") == "0.25.0", "producer version pins")

    with TemporaryDirectory(prefix="silmaril-brotli-raw-") as path:
        work = Path(path)
        source = args.brotli_source.resolve() if args.brotli_source else work / "brotli"
        if args.brotli_source is None:
            run("git", "init", "-q", source)
            run("git", "-C", source, "fetch", "-q", "--depth=1", "https://github.com/google/brotli.git", PIN)
            run("git", "-C", source, "checkout", "-q", "--detach", "FETCH_HEAD")
        require(run("git", "-C", source, "rev-parse", "HEAD").decode().strip() == PIN, "Brotli SHA")
        require(run("git", "-C", source, "diff", "HEAD", "--") == b"", "modified Brotli source")
        build = work / "build"
        run("cmake", "-S", source, "-B", build, "-DCMAKE_BUILD_TYPE=Release", "-DBUILD_TESTING=OFF")
        run("cmake", "--build", build, "--target", "brotli", "--parallel", "4")
        cli = build / "brotli"
        require(run(cli, "--version").strip() == b"brotli 1.2.0", "native version")
        print(f"libbrotli v1.2.0 {PIN}", flush=True)

        def lean(encoded, *, output_cap=2**21, input_cap=None, window_cap=2**24 - 16, steps=8):
            input_path, output_path = work / "input.br", work / "lean.out"
            input_path.write_bytes(encoded)
            output_path.unlink(missing_ok=True)
            cap = len(encoded) if input_cap is None else input_cap
            result = subprocess.run(
                ["lake", "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true", "--run",
                 HERE / "Interop.lean", input_path, output_path, str(cap), str(output_cap),
                 str(window_cap), str(steps)], cwd=ROOT, capture_output=True, text=True)
            if result.returncode == 3:
                require(not output_path.exists(), "rejecting decoder wrote partial output")
                return result.stdout.strip().rsplit(".", 1)[-1]
            require(result.returncode == 0, result.stdout + result.stderr)
            return output_path.read_bytes()

        fixture = {"brotli_commit": PIN, "pyarrow": pa.__version__, "thrift": version("thrift"),
                   "accepted": {}, "rejections": {}}

        def accepts(name, encoded, expected, wbits, count, file=None):
            require(run(cli, "--decompress", "--stdout", data=encoded) == expected, name + " native output")
            require(lean(encoded, output_cap=len(expected), window_cap=2**wbits - 16, steps=count) == expected,
                    name + " Lean output")
            fixture["accepted"][name] = {"wire_bytes": len(encoded), "wire_sha256": digest(encoded),
                 "decoded_bytes": len(expected), "decoded_sha256": digest(expected), "wbits": wbits, "steps": count}
            if file is not None:
                fixture["accepted"][name]["parquet_file"] = file
            print(f"{name}: {len(expected)} bytes matched, SHA-256 {digest(encoded)}", flush=True)

        def rejects(name, encoded, reason, *, native_status="rejects", **caps):
            observed = lean(encoded, **caps)
            require(observed == reason, f"{name}: expected {reason}, got {str(observed)[:120]}")
            if native_status == "rejects":
                native = subprocess.run([cli, "--decompress", "--stdout"], input=encoded, capture_output=True)
                require(native.returncode != 0, f"{name}: native unexpectedly accepted")
            fixture["rejections"][name] = {"wire_sha256": digest(encoded), "error": reason,
                                           "native": native_status, "limits": caps}
            print(f"{name}: {reason}, native {native_status}", flush=True)

        raw = b"".join(sha256(i.to_bytes(4, "little")).digest() for i in range(4096))
        streams = {}
        for name, expected, count in (("empty", b"", 1), ("one-byte", raw[:1], 2), ("multiblock", raw, 3)):
            wire = run(cli, "--stdout", "-q", "0", "-w", "16", data=expected)
            accepts(name, wire, expected, 18, count)
            streams[name] = wire
        wire, parquet = parquet_payload(work, raw[:4096])
        accepts("pyarrow-parquet-v1", wire, raw[:4096], 22, 2, parquet)

        # Cover both canonical transitions with exact caps and native replay.
        alphabet = bytes(range(251))
        for count, nibbles in ((65536, 4), (65537, 5), (1048576, 5), (1048577, 6)):
            plain = (alphabet * ((count + 250) // 251))[:count]
            accepts(f"length-{count}", raw_stream(plain, 15, 4, nibbles), plain, 24, 2)
        accepts("long-window-code", raw_stream(b"abcd", 0x21, 7, 4), b"abcd", 10, 2)

        one = streams["one-byte"]
        multi = streams["multiblock"]
        two_raw = bytes.fromhex("00 00 10 61 00 00 08 62 03")
        nonzero_raw_padding = two_raw[:2] + bytes([0x30]) + two_raw[3:]
        require(run(cli, "--decompress", "--stdout", data=two_raw) == b"ab", "raw alignment fixture base")
        for name, encoded, reason in (
            ("empty-input", b"", "truncated"),
            ("truncated-header", one[:2], "truncated"),
            ("truncated-body", one[:3], "truncated"),
            ("missing-terminal", one[:-1], "truncated"),
            ("reserved-wbits", b"\x11", "reservedWindow"),
            ("reserved-metadata", bytes.fromhex("1c 03"), "reservedMetadata"),
            ("leading-zero-length-nibble", raw_stream(b"a", 0, 1, 5), "noncanonicalLength"),
            ("nonzero-terminal-padding", one[:-1] + bytes([one[-1] | 4]), "nonzeroPadding"),
            ("nonzero-raw-padding", nonzero_raw_padding, "nonzeroPadding"),
            ("trailing-byte", one + b"\0", "trailingInput"),
        ):
            rejects(name, encoded, reason)
        meta = bytes.fromhex("0c 03")
        require(run(cli, "--decompress", "--stdout", data=meta) == b"", "native metadata wire")
        rejects("metadata", meta, "unsupportedMetadata", native_status="accepts")
        compressible = b"abcde" * 2048
        compressed = run(cli, "--stdout", "-q", "5", data=compressible)
        require(run(cli, "--decompress", "--stdout", data=compressed) == compressible, "native entropy control")
        rejects("compressed", compressed, "unsupportedCompressed", native_status="accepts")
        for name, reason, caps in (
            ("one-less-input", "inputLimit", {"input_cap": len(multi) - 1}),
            ("one-less-output", "outputLimit", {"output_cap": len(raw) - 1}),
            ("one-less-window", "windowLimit", {"window_cap": 2**18 - 17}),
            ("one-less-step", "stepLimit", {"steps": 2}),
        ):
            rejects(name, multi, reason, native_status="not compared for caller cap", **caps)

        manifest = HERE / "fixtures.json"
        require(fixture == json.loads(manifest.read_text()), "pinned fixtures differ")


if __name__ == "__main__":
    main()
