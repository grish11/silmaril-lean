#!/usr/bin/env python3
"""Choose the Lake targets that `lean / check on prove` sends to the prove client.

A pull request builds the targets `make -s scope BASE=HEAD^1` narrows from the full list
(`make -s scope`, the list main pushes build). The prove client passes
`CHECK_TARGETS=<targets>` as one argv element, and its `RunRequest` rejects an element of more
than 4096 characters (silmaril-lean#752). When the narrowed list would come within HEADROOM of that
limit, this falls back to the full list, which covers every narrowed target: a `+Module` target is
covered by a library of the full list whose globs or roots match the module, and any other target
must be in the full list. It never truncates or drops targets: if the full list is too long, or a
narrowed target is not covered, it fails.

Usage: ci-targets.py --scoped TARGETS --full TARGETS [--lakefile lakefile.toml]
Prints the chosen targets on stdout and the reason on stderr.
"""

import argparse
import sys
import tomllib
from pathlib import Path

LIMIT = 4096
HEADROOM = 256
PREFIX = "CHECK_TARGETS="


class TargetError(Exception):
    pass


def encoded_length(targets):
    """Length of the argv element the prove client receives, in characters and UTF-8 bytes."""
    element = PREFIX + " ".join(targets)
    return max(len(element), len(element.encode("utf-8")))


def fits(targets, limit=LIMIT, headroom=HEADROOM):
    return encoded_length(targets) <= limit - headroom


def glob_matches(glob, module):
    if glob.endswith(".+"):
        return module.startswith(glob[:-1])
    if glob.endswith(".*"):
        return module == glob[:-2] or module.startswith(glob[:-1])
    return module == glob


def library_modules(lakefile):
    """Map each `lean_lib` name to its module patterns (globs, else roots, else its name)."""
    with open(lakefile, "rb") as f:
        data = tomllib.load(f)
    libs = {}
    for lib in data.get("lean_lib", []):
        roots = lib.get("roots") or [lib["name"]]
        libs[lib["name"]] = list(lib.get("globs") or []) + list(roots)
    return libs


def uncovered(scoped, full, libs):
    """The narrowed targets that no target of the full list covers."""
    full_set = set(full)
    missing = []
    for t in scoped:
        if t.startswith("+"):
            module = t[1:]
            if not any(glob_matches(g, module)
                       for name in full if name in libs for g in libs[name]):
                missing.append(t)
        elif t not in full_set:
            missing.append(t)
    return missing


def choose(scoped, full, libs, limit=LIMIT, headroom=HEADROOM):
    """Return (targets, reason)."""
    if fits(scoped, limit, headroom):
        return scoped, f"scoped targets ({encoded_length(scoped)} characters)"
    missing = uncovered(scoped, full, libs)
    if missing:
        raise TargetError("the full target list does not cover the scoped targets "
                          + " ".join(missing) + "; not falling back")
    if not fits(full, limit, headroom):
        raise TargetError(f"the full target list is {encoded_length(full)} characters, over "
                          f"{limit} - {headroom}; it needs a non-argv transport")
    return full, (f"scoped targets are {encoded_length(scoped)} characters, over {limit} - "
                  f"{headroom} (silmaril-lean#752); building the full list main pushes build, "
                  f"which covers all {len(scoped)} scoped targets")


def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument("--scoped", required=True)
    ap.add_argument("--full", required=True)
    ap.add_argument("--lakefile", default=str(Path(__file__).resolve().parent.parent / "lakefile.toml"))
    args = ap.parse_args(argv)
    try:
        targets, reason = choose(args.scoped.split(), args.full.split(),
                                 library_modules(args.lakefile))
    except TargetError as e:
        print(f"ci-targets: {e}", file=sys.stderr)
        return 1
    print(f"ci-targets: {reason}", file=sys.stderr)
    print(" ".join(targets))
    return 0


if __name__ == "__main__":
    sys.exit(main())
