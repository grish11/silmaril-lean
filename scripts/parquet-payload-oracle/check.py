#!/usr/bin/env python3
"""Extract and check actual Parquet V1 page payloads from the pinned PyArrow writer."""
from hashlib import sha256
from importlib.metadata import version
from pathlib import Path
from struct import pack
import subprocess
from tempfile import TemporaryDirectory

import pyarrow as pa
import pyarrow.parquet as pq
from thrift.Thrift import TType
from thrift.protocol.TCompactProtocol import TCompactProtocol
from thrift.transport.TTransport import TMemoryBuffer

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
VALUES = [0, 1, 0, -1] * 16


def require(condition, label):
    if not condition:
        raise SystemExit(label)


def fields(reader, wanted):
    found = {}
    reader.readStructBegin()
    while True:
        _, ty, number = reader.readFieldBegin()
        if ty == TType.STOP:
            break
        if number in wanted:
            expected, read = wanted[number]
            require(ty == expected and number not in found, f"incorrect Thrift field {number}")
            found[number] = read(reader)
        else:
            reader.skip(ty)
        reader.readFieldEnd()
    reader.readStructEnd()
    require(found.keys() == wanted.keys(), "missing Thrift fields")
    return found


def one_struct(reader, read):
    ty, count = reader.readListBegin()
    require(ty == TType.STRUCT and count == 1, "expected one element")
    value = read(reader)
    reader.readListEnd()
    return value


def column_codec(reader):
    return fields(reader, {4: (TType.I32, TCompactProtocol.readI32)})[4]


def chunk_codec(reader):
    return fields(reader, {3: (TType.STRUCT, column_codec)})[3]


def group_codec(reader):
    return fields(reader, {1: (TType.LIST, lambda p: one_struct(p, chunk_codec))})[1]


def footer_codec(data):
    require(data[:4] == data[-4:] == b"PAR1", "expected a plaintext Parquet file")
    length = int.from_bytes(data[-8:-4], "little")
    wire = TCompactProtocol(TMemoryBuffer(data[-8-length:-8]))
    return fields(wire, {4: (TType.LIST, lambda p: one_struct(p, group_codec))})[4]


def extract(codec, compression):
    schema = pa.schema([pa.field("x", pa.int32(), nullable=False)])
    table = pa.Table.from_arrays([pa.array(VALUES, type=pa.int32())], schema=schema)
    sink = pa.BufferOutputStream()
    pq.write_table(table, sink, compression=compression, data_page_version="1.0",
                   version="2.6", row_group_size=len(VALUES), use_dictionary=False,
                   column_encoding="PLAIN", write_statistics=False, write_page_checksum=False)
    data = sink.getvalue().to_pybytes()
    parquet = pq.ParquetFile(pa.BufferReader(data))
    require(parquet.read().column("x").to_pylist() == VALUES, "PyArrow row readback")
    require(footer_codec(data) == codec, "unexpected numeric CompressionCodec ID")
    leaf = parquet.schema.column(0)
    require(leaf.max_definition_level == leaf.max_repetition_level == 0, "expected a required flat leaf")
    column = parquet.metadata.row_group(0).column(0)
    require(not column.has_dictionary_page, "unexpected dictionary page")
    offset = column.data_page_offset
    transport = TMemoryBuffer(data[offset:offset + column.total_compressed_size])
    i32 = (TType.I32, TCompactProtocol.readI32)
    header = fields(TCompactProtocol(transport), {1: i32, 2: i32, 3: i32})
    require(header[1] == 0, "expected DATA_PAGE V1")
    header_length = transport.cstringio_buf.tell()
    compressed, decoded = header[3], header[2]
    require(header_length + compressed == column.total_compressed_size, "expected one compressed page")
    require(header_length + decoded == column.total_uncompressed_size, "uncompressed extent mismatch")
    payload = transport.readAll(compressed)
    digest = sha256(payload).hexdigest()
    print(f"{compression}: codec={codec} file={sha256(data).hexdigest()} "
          f"offset={offset + header_length} compressed={compressed} decoded={decoded} payload={digest}")
    return payload, decoded


def lean(work, payload, codec, decoded, *, csize=None, climit=None, ulimit=None, calls=512):
    source, target = work / "page.bin", work / "out.bin"
    source.write_bytes(payload)
    target.unlink(missing_ok=True)
    compressed = len(payload) if csize is None else csize
    compressed_limit = compressed if climit is None else climit
    decoded_limit = decoded if ulimit is None else ulimit
    args = (codec, compressed, compressed_limit, decoded, decoded_limit, calls)
    result = subprocess.run(
        ["lake", "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true", "--run",
         HERE / "Interop.lean", source, target, *map(str, args)],
        cwd=ROOT, stdout=subprocess.PIPE, text=True,
    )
    if result.returncode == 3:
        return result.stdout.strip()
    result.check_returncode()
    return target.read_bytes()


def main():
    require(pa.__version__ == "26.0.1" and version("thrift") == "0.25.0", "oracle versions")
    decoded = pack("<" + "i" * len(VALUES), *VALUES)
    with TemporaryDirectory(prefix="silmaril-parquet-payload-") as directory:
        work = Path(directory)
        payloads = {}
        for codec, compression in ((0, "NONE"), (1, "snappy"), (2, "gzip"), (7, "lz4")):
            payload, size = extract(codec, compression)
            require(size == len(decoded), "expected PLAIN INT32 bytes")
            require(lean(work, payload, codec, size) == decoded, f"{compression}: payload decode")
            payloads[codec] = payload
        print(f"four extracted V1 payloads decoded exactly, sha256 PLAIN={sha256(decoded).hexdigest()}")
        snappy, gzip, lz4 = (payloads[i] for i in (1, 2, 7))
        corrupt_crc = gzip[:-8] + bytes([gzip[-8] ^ 1]) + gzip[-7:]
        cases = [
            ("Snappy declared as uncompressed", snappy, 0, 256, {}, "outputSizeMismatch"),
            ("LZ4_RAW declared as deprecated LZ4", lz4, 5, 256, {}, "unsupportedCodec 5"),
            ("unknown codec", snappy, -1, 256, {}, "unsupportedCodec -1"),
            ("Snappy truncated", snappy[:-1], 1, 256, {}, "malformed 1"),
            ("Snappy suffix", snappy + b"\x00", 1, 256, {}, "trailingInput 1"),
            ("LZ4_RAW suffix", lz4 + b"\x00", 7, 256, {}, "malformed 7"),
            ("GZIP suffix", gzip + b"\x00", 2, 256, {}, "trailingInput 2"),
            ("GZIP second member", gzip + gzip, 2, 256, {}, "trailingInput 2"),
            ("GZIP CRC", corrupt_crc, 2, 256, {}, "malformed 2"),
            ("GZIP truncated trailer", gzip[:-1], 2, 256, {"calls": 64}, "gzipIncomplete"),
            ("GZIP output smaller than expected", gzip, 2, 257, {}, "outputSizeMismatch"),
            ("GZIP output would exceed expected", gzip, 2, 32, {"ulimit": 256}, "outputSizeMismatch"),
            ("GZIP call budget", gzip, 2, 256, {"calls": 0}, "gzipIncomplete"),
            ("compressed size", gzip, 2, 256, {"csize": len(gzip) - 1}, "compressedSizeMismatch"),
            ("compressed cap", gzip, 2, 256, {"climit": len(gzip) - 1}, "compressedLimit"),
            ("output cap", gzip, 2, 256, {"ulimit": 255}, "outputLimit"),
        ]
        for name, payload, codec, size, args, reason in cases:
            got = lean(work, payload, codec, size, **args)
            require(got == reason, f"{name}: expected {reason}, got {got!r}")
            print(f"{name}: {reason}")


if __name__ == "__main__":
    main()
