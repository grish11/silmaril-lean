#!/usr/bin/env python3
"""Inventory ACL2 8.7 x86isa build dependencies and optional certificate evidence."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile


TAG = "8.7"
COMMIT = "bc6f4f49e81a0711214a8d91f0d06e0e084d2204"
PROJECT = "projects/x86isa"
ROOTS = ("machine/x86", "tools/execution/top", "top")
NATIVE_INPUTS = (
    "machine/syscalls.acl2",
    "machine/x86isa_full_exec_support.lisp",
    "machine/shared/libsyscallutils.so",
)
MAKE_TOKEN = re.compile(r'\s+|;[^\n]*|[()]|:[A-Z_0-9-]+|"(?:[^"\\]|\\.)*"')


def read_make_data(path):
    """Read the restricted S-expression format emitted by cert.pl --smakefile."""
    stack = [[]]
    data = path.read_text()
    offset = 0
    while offset < len(data):
        match = MAKE_TOKEN.match(data, offset)
        if not match:
            raise ValueError(f"Unexpected cert.pl syntax at offset {offset}")
        token = match[0]
        offset = match.end()
        if token == "(":
            group = []
            stack[-1].append(group)
            stack.append(group)
        elif token == ")":
            if len(stack) == 1:
                raise ValueError("Unbalanced cert.pl data")
            stack.pop()
        elif token.startswith('"'):
            stack[-1].append(re.sub(r"\\(.)", r"\1", token[1:-1]))
        elif token.startswith(":"):
            stack[-1].append(token)
    if len(stack) != 1 or len(stack[0]) != 1:
        raise ValueError("Unbalanced cert.pl data")
    return {key: values for key, *values in stack[0][0]}


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def book_path(path, books):
    return path.resolve().relative_to(books).as_posix()


def scan(books, acl2, root, scratch, log, env):
    project = books / PROJECT
    makefile = scratch / "deps.mk"
    other = scratch / "other"
    with log.open("w") as output:
        subprocess.run(
            [books / "build/cert.pl", "--acl2", acl2, "--acl2-books", books,
             "--makefile-only", "--smakefile", "-o", makefile,
             "--write-otherdeps", other, root],
            cwd=project, env=env, check=True, stdout=output, stderr=subprocess.STDOUT,
        )
    data = read_make_data(makefile.with_suffix(".mk.lsp"))

    def normalize(names):
        return sorted({book_path(project / name, books) for name in names})

    dependencies = {}
    for target, *inputs in data[":DEPENDENCY-MAP"]:
        name = book_path(project / target, books)
        dependencies.setdefault(name, set()).update(normalize(inputs))
    certs = normalize(data[":CERT_PL_CERTS"])
    if f"{PROJECT}/{root}.cert" not in certs:
        raise ValueError(f"cert.pl did not report the target {root}")
    return {
        "certificates": certs,
        "sources": normalize(data[":CERT_PL_SOURCES"]),
        "other_inputs": normalize(other.read_text().splitlines()),
        "make_dependencies": {key: sorted(values) for key, values in dependencies.items()},
        "feature_sets": {
            key.removeprefix(":CERT_PL_"): normalize(values)
            for key, values in data.items()
            if key.startswith(":CERT_PL_") and values
            and key not in {":CERT_PL_CERTS", ":CERT_PL_ALLCERTS", ":CERT_PL_SOURCES"}
        },
    }


def lisp_string(path):
    return '"' + str(path).replace("\\", "\\\\").replace('"', '\\"') + '"'


def audit(books, acl2, root, scratch, out, env):
    project = books / PROJECT
    book = project / root
    name = root.replace("/", "-")
    records = scratch / "records.tsv"
    sample = scratch / "world.lsp"
    support = Path(__file__).resolve().with_name("certificate.lisp")
    # Use a fresh image for each root so that its include-book world is isolated.
    commands = (
        "(set-ld-error-action '(:exit 1) state)\n"
        f'(include-book {lisp_string(root)} :ttags :all :uncertified-okp nil)\n'
        f':q\n(handler-case (progn (load {lisp_string(support)})\n'
        f'  (c1-audit {lisp_string(book)} {lisp_string(records)} '
        f'{lisp_string(sample)}) (sb-ext:exit :code 0))\n'
        '  (error (condition) (format *error-output* "~a~%" condition) (sb-ext:exit :code 1)))\n'
    )
    log = out / f"{name}.audit.log"
    with log.open("w") as output:
        result = subprocess.run([acl2], input=commands, text=True, cwd=project, env=env,
                                stdout=output, stderr=subprocess.STDOUT)
    if result.returncode or not (records.is_file() and sample.is_file()):
        raise SystemExit(f"ACL2 audit did not complete for {root}. See {log}")
    phases = {phase: [] for phase in ("pre", "post", "live")}
    for row in records.read_text().splitlines():
        phase, visibility, path, skipped, axioms, tags = row.split("\t")
        phases[phase].append({
            "source": book_path(Path(path), books), "visibility": visibility,
            "skipped_proofs": skipped, "axioms": axioms,
            "trust_tags": tags.split(",") if tags else [],
        })
    phases["world_sample_sha256"] = digest(sample)
    (out / f"{name}.world.lsp").write_bytes(sample.read_bytes())
    (out / f"{name}.certificate.sha256").write_text(
        f"{digest(book.with_suffix('.cert'))}  {PROJECT}/{root}.cert\n"
    )
    return phases


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("checkout", type=Path, help="ACL2 git checkout at the pinned commit")
    parser.add_argument("output", type=Path)
    parser.add_argument("--acl2", type=Path, help="ACL2 8.7 executable (default: checkout/saved_acl2)")
    parser.add_argument("--root", choices=ROOTS, action="append", help="default: all three roots")
    parser.add_argument("--native-inputs", action="store_true", help="scan Linux X86ISA_EXEC=t inputs")
    parser.add_argument("--certified", action="store_true", help="also audit completed certificates using SBCL")
    args = parser.parse_args()
    checkout = args.checkout.resolve()
    books = checkout / "books"
    project = books / PROJECT
    acl2 = (args.acl2 or checkout / "saved_acl2").resolve()
    out = args.output.resolve()
    if subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=checkout, text=True).strip() != COMMIT:
        parser.error(f"use the ACL2 {TAG} checkout at {COMMIT}")
    if subprocess.run(["git", "diff", "--quiet", "HEAD", "--"], cwd=checkout).returncode:
        parser.error("the ACL2 checkout has tracked changes")
    native = [project / name for name in NATIVE_INPUTS]
    if args.native_inputs and not all(path.is_file() for path in native):
        parser.error("generate the Linux X86ISA_EXEC=t inputs with the upstream Makefile first")
    if not args.native_inputs and any(path.exists() for path in native[:2]):
        parser.error("use a fresh X86ISA_EXEC=nil checkout without generated syscall sources")

    out.mkdir(parents=True, exist_ok=True)
    env = {**os.environ, "ACL2_CUSTOMIZATION": "NONE", "ACL2_SYSTEM_BOOKS": str(books),
           "CERT_PL_NO_COLOR": "1", "LC_ALL": "C",
           "X86ISA_EXEC": "t" if args.native_inputs else "nil"}
    result = {
        "acl2_tag": TAG, "acl2_commit": COMMIT, "x86isa_exec": env["X86ISA_EXEC"],
        "native_make_inputs": [book_path(path, books) for path in native] if args.native_inputs else [],
        "roots": {},
    }
    for root in dict.fromkeys(args.root or ROOTS):
        with tempfile.TemporaryDirectory(prefix="acl2-x86isa-") as directory:
            scratch = Path(directory)
            name = root.replace("/", "-")
            build = scan(books, acl2, root, scratch, out / f"{name}.scan.log", env)
            row = {"source_sha256": digest(project / f"{root}.lisp"), "cert_pl": build}
            if args.certified:
                row["certificate_evidence"] = audit(books, acl2, root, scratch, out, env)
            result["roots"][root] = row
            print(f"{root}: {len(build['certificates'])} cert targets, "
                  f"{len(build['sources'])} sources, {len(build['other_inputs'])} other inputs")
    manifest = out / "manifest.json"
    manifest.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(f"{digest(manifest)}  {manifest}")


if __name__ == "__main__":
    main()
