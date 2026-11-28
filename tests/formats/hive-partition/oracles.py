"""Check the shared fixtures against PyArrow and the Apache Hive release."""

import argparse
import hashlib
import json
import subprocess
from pathlib import Path

import pyarrow as pa
import pyarrow.dataset as ds


HERE = Path(__file__).resolve().parent
JARS = {
    "hive-common-4.1.0.jar": "8e62f91679455f2dcb4810ea4d29910968bfbf819dc64e1900afd0322b0f18f5",
    "hadoop-client-api-3.4.1.jar": "a964d4daa054c9615bbafb4553efbb140fa7fb9ac6f358a24393f183a5703438",
    "slf4j-api-1.7.36.jar": "d3ef575e3e4979678dc01bf1dcce51021493b4d11fb7f1be8ad982877c16a1c0",
}


def check_arrow(fixtures):
    assert pa.__version__ == "26.0.1", pa.__version__
    for fixture in fixtures:
        path = fixture["path"]
        entries = fixture["entries"]
        partition = ds.HivePartitioning(pa.schema([(key, pa.string()) for key, _ in entries]))
        # An ending slash tells Arrow that the last path component is a directory.
        expression = partition.parse(path + "/")
        assert ds.get_partition_keys(expression) == dict(entries), (path, expression)
        if fixture["canonical"]:
            assert partition.format(expression) == (path, ""), (path, expression)


def check_hive(fixtures, jar_dir):
    for name, expected in JARS.items():
        with (jar_dir / name).open("rb") as stream:
            assert hashlib.file_digest(stream, "sha256").hexdigest() == expected, name

    command = ["java", "-cp", str(jar_dir / "*"), str(HERE / "HiveOracle.java")]
    for fixture in fixtures:
        fields = []
        for key, value in fixture["input"]:
            fields.extend([key, "null" if value is None else "text", value or ""])
        completed = subprocess.run(command + fields, check=True, text=True, capture_output=True)
        assert completed.stdout.rstrip("\n") == fixture["path"], (fields, completed.stdout)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--hive-jars", type=Path, required=True)
    args = parser.parse_args()
    fixtures = json.loads((HERE / "fixtures.json").read_text(encoding="utf-8"))
    check_arrow(fixtures["arrow"])
    check_hive(fixtures["hive"], args.hive_jars)
    print(f'Checked {len(fixtures["arrow"])} PyArrow and {len(fixtures["hive"])} Apache Hive fixtures')


if __name__ == "__main__":
    main()
