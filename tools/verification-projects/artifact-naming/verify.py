#!/usr/bin/env python3
"""External assurance for exact binary DASL/BDASL CIDs, not Lean proof generation."""

import argparse
import hashlib
import subprocess
import sys
from pathlib import Path

from manifest import read_hex, read_manifest


PROFILES = {"dasl": {"sha256"}, "bdasl": {"sha256", "blake3"}}
ALGORITHMS = {"sha256": 0x12, "blake3": 0x1E}
CODECS = {"raw": 0x55, "drisl": 0x71}


def digest(algorithm, payload):
    if algorithm == "sha256":
        return hashlib.sha256(payload).digest()
    result = subprocess.run(
        ["b3sum", "--no-names"], input=payload, capture_output=True, check=True, timeout=30
    )
    return read_hex(result.stdout.decode("ascii").strip())


def prefix(profile, codec, algorithm):
    if profile not in PROFILES or algorithm not in PROFILES[profile] or codec not in CODECS:
        raise ValueError("unsupported profile/codec/algorithm combination")
    return bytes((1, CODECS[codec], ALGORITHMS[algorithm], 32))


def verify_manifest(path):
    rows = read_manifest(path)
    seen = {}
    for identifier, row in rows.items():
        try:
            expected_prefix = prefix(row.profile, row.codec, row.algorithm)
            if len(row.name) != 36 or not row.name.startswith(expected_prefix):
                raise ValueError("CID version, codec, algorithm or digest boundary mismatch")
            if row.name in seen and seen[row.name] != row.payload:
                raise ValueError("conflicting payloads under the same binary CID")
            seen[row.name] = row.payload
        except ValueError as error:
            raise ValueError(f"{identifier}: {error}") from error
    for identifier, row in rows.items():
        if row.name[4:] != digest(row.algorithm, row.payload):
            raise ValueError(f"{identifier}: digest mismatch")
    return len(rows)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    verify = commands.add_parser("verify")
    verify.add_argument("manifest", type=Path)
    name = commands.add_parser("name", help="compute an external CID over exact input bytes")
    for field, choices in (("profile", PROFILES), ("codec", CODECS), ("algorithm", ALGORITHMS)):
        name.add_argument(field, choices=choices)
    name.add_argument("input", help="file containing the payload, or - for stdin")
    args = parser.parse_args()
    try:
        if args.command == "verify":
            print(f"externally verified {verify_manifest(args.manifest)} row(s)")
        else:
            head = prefix(args.profile, args.codec, args.algorithm)
            payload = sys.stdin.buffer.read() if args.input == "-" else Path(args.input).read_bytes()
            result = digest(args.algorithm, payload)
            if len(result) != 32:
                raise ValueError("unexpected digest size")
            print((head + result).hex())
    except (OSError, ValueError, subprocess.SubprocessError) as error:
        parser.exit(1, f"artifact-naming: {error}\n")


if __name__ == "__main__":
    main()
