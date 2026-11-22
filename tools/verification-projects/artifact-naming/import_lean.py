#!/usr/bin/env python3
"""Emit declared bytes as Lean literals. This is not a verification command."""

import argparse
from pathlib import Path

from manifest import read_manifest


def lean_literal(data):
    return "[" + ", ".join(f"0x{byte:02x}" for byte in data) + "]"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("manifest", type=Path)
    args = parser.parse_args()
    try:
        rows = read_manifest(args.manifest)
    except (OSError, ValueError) as error:
        parser.exit(1, f"artifact-import: {error}\n")
    print("module\n\n@[expose] public section\n\nnamespace ArtifactNamingRows\n")
    for identifier, row in rows.items():
        print(f"def name_{identifier} : List UInt8 := {lean_literal(row.name)}")
        print(f"def bytes_{identifier} : List UInt8 := {lean_literal(row.payload)}\n")
    print("end ArtifactNamingRows")


if __name__ == "__main__":
    main()
