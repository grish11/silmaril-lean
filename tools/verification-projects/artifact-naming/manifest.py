"""Read artifact declarations without interpreting or verifying their names."""

import re
from typing import NamedTuple


HEADER = "id\tprofile\tcodec\talgorithm\tcid_hex\tpayload_hex"


class Row(NamedTuple):
    profile: str
    codec: str
    algorithm: str
    name: bytes
    payload: bytes


def read_hex(text):
    if not re.fullmatch(r"(?:[0-9a-f]{2})*", text):
        raise ValueError("expected complete lowercase hex bytes")
    return bytes.fromhex(text)


def read_manifest(path):
    header, *lines = path.read_text(encoding="ascii").splitlines() or [""]
    if header != HEADER or not lines:
        raise ValueError("expected a nonempty manifest with the v1 TSV header")
    rows = {}
    for number, line in enumerate(lines, 2):
        try:
            identifier, profile, codec, algorithm, name_hex, payload_hex = line.split("\t")
            if not re.fullmatch(r"[a-z][a-z0-9_]*", identifier) or identifier in rows:
                raise ValueError("invalid or duplicate row identifier")
            if not payload_hex:
                raise ValueError("use '-' for the empty payload")
            name = read_hex(name_hex)
            payload = b"" if payload_hex == "-" else read_hex(payload_hex)
            rows[identifier] = Row(profile, codec, algorithm, name, payload)
        except ValueError as error:
            raise ValueError(f"line {number}: {error}") from error
    return rows
