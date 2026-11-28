"""Check bounded Lean timestamp slots on pinned PyArrow PLAIN data pages."""

import hashlib
from importlib.metadata import version
import json
import os
from pathlib import Path
from runpy import run_path
import subprocess
import tempfile

import pyarrow as pa
import pyarrow.parquet as pq
from thrift.protocol.TCompactProtocol import TCompactProtocol
from thrift.transport.TTransport import TMemoryBuffer


ROOT = Path(__file__).resolve().parents[3]
HEADER_FIELDS = run_path(str(ROOT / "scripts/parquet-scalar-page/PyArrowOracle.py"))["header_fields"]
FIXTURE_SHA256 = "feb5b71f768a7a3ebd0b4776c91753c653114270af43d9fc45dc99e93ad24057"
UNITS = {"ms": "millis", "us": "micros", "ns": "nanos"}
MIXED = [None, -(2**63), -2001, None, -1, 0, None, 2**63 - 1]
PROFILES = (("1.0", "NONE", 0), ("2.0", "NONE", 0), ("2.0", "SNAPPY", 1))


def columns():
    for unit in UNITS:
        for adjusted in (False, True):
            values = MIXED if adjusted else list(reversed(MIXED))
            yield unit + ("_utc" if adjusted else "_local"), unit, adjusted, True, values
    yield "required_i64_timestamp", "us", True, False, [-(2**63), -2001, -2, -1, 0, 1, 9, 2**63 - 1]
    yield "all_null", "ns", False, True, [None] * len(MIXED)


def table_from_cases(cases):
    fields, arrays = [], []
    for name, unit, adjusted, nullable, values in cases:
        type_ = pa.timestamp(unit, "UTC" if adjusted else None)
        fields.append(pa.field(name, type_, nullable=nullable))
        arrays.append(pa.array(values, type=pa.int64()).cast(type_))
    return pa.Table.from_arrays(arrays, schema=pa.schema(fields))


def page_parts(data, column, page_version, codec, count, nulls):
    assert not column.has_dictionary_page
    assert column.compression == {0: "UNCOMPRESSED", 1: "SNAPPY"}[codec]
    offset = column.data_page_offset
    size = column.total_compressed_size
    page = data[offset:offset + size]
    transport = TMemoryBuffer(page)
    header = HEADER_FIELDS(TCompactProtocol(transport), (5, 8))
    header_length = transport.cstringio_buf.tell()
    assert header_length + header[3] == size
    assert header_length + header[2] == column.total_uncompressed_size
    if page_version == "1.0":
        assert header[1] == 0 and header[5][1] == count and header[5][2] == 0
    else:
        assert header[1] == 3 and header[8][4] == 0 and header[8][6] == 0
        assert header[8][1] == header[8][3] == count and header[8][2] == nulls
    return page[:header_length], transport.readAll(header[3])


def fixture(lines, directory, digest, index, page_version, compression, codec, cases, table):
    sink = pa.BufferOutputStream()
    pq.write_table(table, sink, version="2.6", data_page_version=page_version,
                   compression=compression, use_dictionary=False, column_encoding="PLAIN",
                   store_schema=False, write_statistics=False, write_page_checksum=False,
                   row_group_size=len(MIXED))
    data = sink.getvalue().to_pybytes()
    digest.update(len(data).to_bytes(8, "little"))
    digest.update(data)
    file = directory / f"fixture-{index}.parquet"
    file.write_bytes(data)
    parquet = pq.ParquetFile(pa.BufferReader(data))
    assert parquet.metadata.num_row_groups == 1
    readback = parquet.read()
    lines.extend([
        f"private def fixture{index} : IO Unit := do",
        f"  let file : Bytes := ⟨← IO.FS.readBinFile {json.dumps(str(file))}⟩",
    ])
    for i, (name, unit, adjusted, nullable, values) in enumerate(cases):
        leaf = parquet.schema.column(i)
        assert leaf.name == name and leaf.physical_type == "INT64"
        assert leaf.max_repetition_level == 0 and leaf.max_definition_level == int(nullable)
        logical = json.loads(leaf.logical_type.to_json())
        assert logical["Type"] == "Timestamp" and logical["isAdjustedToUTC"] == adjusted
        assert readback[name].type.unit == unit
        assert readback[name].cast(pa.int64()).to_pylist() == values
        header, body = page_parts(data, parquet.metadata.row_group(0).column(i), page_version, codec,
                                  len(values), values.count(None))
        expected = "[" + ", ".join("none" if x is None else f"some ({x})" for x in values) + "]"
        lines.append(f'  checkPage file {i + 1} "{name}" .{UNITS[unit]} {str(adjusted).lower()} '
                     f'{int(nullable)} {codec} {list(header)} {list(body)} {expected} '
                     f'{str(index == 1 and i == 0).lower()}')


HARNESS = '''module
import Silmaril.Formats.Parquet.Timestamp.Page.Defs
meta import Silmaril.Formats.Parquet.Timestamp.Page.Defs
meta import Silmaril.Formats.Parquet.Timestamp.Defs
meta import Silmaril.Formats.Parquet.Page.Header.Defs
meta import Silmaril.Formats.Parquet.ScalarPage.Defs
meta import Silmaril.Formats.Parquet.Footer.Defs
meta import Silmaril.Formats.ColumnarTimestamp.Defs
meta import Silmaril.Numeric.Timestamp.Defs
meta import Silmaril.Formats.Bytes
open Silmaril.Formats Silmaril.Formats.Parquet Silmaril.Numeric.Timestamp
private def limits : ScalarPage.Limits := ⟨4096, 4096, ⟨4096, 128⟩, 0⟩
private def check (test : Bool) (label : String) : IO Unit :=
  unless test do throw (IO.userError label)
private def require {α ε : Type} [Repr ε] (result : Except ε α) : IO α :=
  match result with
  | .ok value => pure value
  | .error reason => throw (IO.userError s!"{repr reason}")
private def expectError (binding : Timestamp.Binding)
    (result : Except Timestamp.Page.Error (List (Option (Timestamp.Page.Value binding))))
    (reason : Timestamp.Page.Error) : IO Unit :=
  match result with
  | .error actual => check (reason == actual) s!"expected {repr reason}, got {repr actual}"
  | .ok _ => throw (IO.userError s!"accepted invalid page for {repr reason}")
private def checkFailures (binding : Timestamp.Binding) (schema : FlatPage.LevelSchema)
    (codec : Int) (header : Page.Header) (body : Bytes) : IO Unit := do
  let decode := Timestamp.Page.decode binding schema codec
  expectError binding (decode header limits (body.push 0)) (.scalar (.payload .compressedSizeMismatch))
  expectError binding (decode { header with compressedSize := header.compressedSize + 1 } limits body)
    (.scalar (.payload .compressedSizeMismatch))
  expectError binding (decode header { limits with compressedBytes := 0 } body)
    (.scalar (.payload .compressedLimit))
  expectError binding (decode header { limits with levels := { limits.levels with values := 0 } } body)
    (.scalar (.levels .countLimit))
  expectError binding (Timestamp.Page.decode binding ⟨0, 0⟩ codec header limits body) .schemaLevels
  expectError binding (Timestamp.Page.decode binding ⟨1, 1⟩ codec header limits body) .schemaLevels
  let wrong : Timestamp.Binding := { binding with leaf := { binding.leaf with repetition := some .repeated } }
  expectError wrong (Timestamp.Page.decode wrong schema codec header limits body) .schemaLevels
  let wrong : Timestamp.Binding := { binding with leaf := { binding.leaf with physicalType := some .int32 } }
  expectError wrong (Timestamp.Page.decode wrong schema codec header limits body) .schemaLevels
  expectError binding (decode { header with kind := .dictionary ⟨0, 0, none⟩ } limits body)
    .unsupportedPage
  let .dataV2 info := header.kind | throw (IO.userError "expected V2 header")
  expectError binding (decode { header with kind := .dataV2 { info with encoding := 8 } } limits body)
    (.scalar (.unsupportedEncoding 8))
  expectError binding (decode { header with kind := .dataV2 { info with numRows := 0 } } limits body)
    (.scalar .invalidRowCount)
  expectError binding (decode { header with kind := .dataV2 { info with numNulls := 0 } } limits body)
    (.scalar (.levels .presentCountMismatch))
  expectError binding (decode { header with kind := .dataV2 { info with definitionBytes := body.length + 1 } }
    limits body) (.scalar .invalidLevelExtent)
private def checkPage (file : Bytes) (index : Nat) (name : String)
    (unit : ColumnarTimestamp.Parquet.TimeUnit) (adjusted : Bool) (definition : Nat)
    (codec : Int) (headerBytes bodyBytes : List UInt8) (expected : List (Option Int))
    (negatives : Bool) : IO Unit := do
  let binding ← require (Timestamp.readFooter {} index file)
  check (binding.leaf.name == name && binding.descriptor.unit == unit &&
    binding.descriptor.isAdjustedToUTC == adjusted) s!"wrong descriptor at {index}"
  let (header, consumed) ← require (Page.readHeaderPrefix {} (Bytes.ofList headerBytes))
  check (consumed == headerBytes.length) s!"header extent at {index}"
  let body := Bytes.ofList bodyBytes
  let schema : FlatPage.LevelSchema := ⟨0, definition⟩
  let slots ← require (Timestamp.Page.decode binding schema codec header limits body)
  check (slots.map (Option.map Ticks.ticks) == expected) s!"slot order, nulls or ticks at {index}"
  if negatives then checkFailures binding schema codec header body
'''


def main():
    assert pa.__version__ == "26.0.1" and version("thrift") == "0.25.0"
    cases = list(columns())
    table = table_from_cases(cases)
    digest = hashlib.sha256()
    with tempfile.TemporaryDirectory() as temporary:
        directory = Path(temporary)
        lines = [HARNESS]
        for index, (page_version, compression, codec) in enumerate(PROFILES):
            fixture(lines, directory, digest, index, page_version, compression, codec, cases, table)
        assert digest.hexdigest() == FIXTURE_SHA256, f"PyArrow file SHA-256 {digest.hexdigest()}"
        lean = directory / "Fixture.lean"
        lean.write_text("\n".join(lines + [f"#eval fixture{i}" for i in range(len(PROFILES))]) + "\n")
        subprocess.run([os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
                        "-DwarningAsError=true", str(lean)], cwd=ROOT, check=True)
    print(f"PyArrow 26.0.1: {len(PROFILES) * len(cases)} exact timestamp pages and 13 malformed inputs passed")
    print(f"Length-framed Parquet fixture SHA-256 {FIXTURE_SHA256}")


if __name__ == "__main__":
    main()
