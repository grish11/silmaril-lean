"""Check complete CSV bridge output against the hash-pinned PyArrow IPC reader."""
import argparse
import hashlib
from pathlib import Path
import runpy


ROOT = Path(__file__).resolve().parents[2]
ORACLE = ROOT / "tests" / "formats" / "arrow-ipc" / "read_writer_fixtures.py"
ASCII_FIXTURE = ROOT / "scripts" / "arrow-to-csv-oracle" / "fixture.py"


def extract_ascii(directory):
    fixture = runpy.run_path(str(ASCII_FIXTURE))
    raw = fixture["read_fixture"]()["csv"]
    assert hashlib.sha256(raw).hexdigest() == fixture["MANIFEST"]["csv_sha256"]
    directory.mkdir(parents=True, exist_ok=True)
    (directory / "ascii.csv").write_bytes(raw)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("directory", type=Path)
    parser.add_argument("--extract-ascii", action="store_true", help="extract the pinned CSV input")
    args = parser.parse_args()
    if args.extract_ascii:
        extract_ascii(args.directory)
        return
    oracle = runpy.run_path(str(ORACLE))
    pa, np, producer = oracle["pa"], oracle["np"], oracle["PRODUCER"]
    assert pa.__version__ == pa.cpp_build_info.version == producer["version"]
    assert np.__version__ == producer["numpy_version"]
    read = oracle["check_stream"]
    read(args.directory, "csv", [("n", True, "int32"), ("text", True, "utf8")],
         [[(-2147483648, 'a,"b"\r\nc'), (None, ""), (2147483647, None), (0, "N")]])
    read(args.directory, "csv-utf8", [("id", False, "int32"), ("café", True, "utf8")],
         [[(-1, "雪"), (0, None), (1, "")]])
    read(args.directory, "named", [("key", False, "int32"), ("café", True, "utf8")],
         [[(7, "λ"), (8, None), (7, ""), (7, "λ")]])
    read(args.directory, "zero-columns", [], [[(), ()]])
    read(args.directory, "empty", [("n", False, "int32")], [[]])


if __name__ == "__main__":
    main()
