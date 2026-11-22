"""Generate a byte-exact witness from two real Git repositories and mount its tree in Lean."""

import hashlib
from pathlib import Path
import subprocess
import sys
import tempfile


def run_fixture(root: Path, algorithm: str, b3sum: Path) -> str:
    repo = root / "git"
    subprocess.run(["git", "init", "--quiet", "--bare", f"--object-format={algorithm}", repo], check=True)

    def git(*args: str, data: bytes | None = None) -> bytes:
        return subprocess.check_output(["git", f"--git-dir={repo}", *args], input=data)

    def blob(data: bytes) -> bytes:
        return git("hash-object", "-w", "--stdin", data=data).strip()

    def tree(*records: bytes) -> bytes:
        return git("mktree", "-z", data=b"\0".join(records) + b"\0").strip()

    executable = blob(b"echo ok\n")
    symlink = blob(b"dir/\xff")
    nested = tree(b"100755 blob " + executable + b"\t\xff")
    parent = tree(b"040000 tree " + nested + b"\tdir", b"120000 blob " + symlink + b"\tlink")
    for name, kind, oid in [("executable", "blob", executable), ("symlink", "blob", symlink),
                            ("nested", "tree", nested), ("root", "tree", parent)]:
        payload = git("cat-file", kind, oid.decode("ascii"))
        header = f"{kind} {len(payload)}\0".encode("ascii")
        if hashlib.new(algorithm, header + payload).hexdigest().encode("ascii") != oid:
            raise RuntimeError(f"incorrect native Git object name for {name}")
        (root / f"{name}.{kind}").write_bytes(payload)
        (root / f"{name}.oid").write_bytes(oid + b"\n")

    run = subprocess.run(["lake", "env", "lean", "-DwarningAsError=true", "--run",
                          "tests/formats/GitFilesystem.lean", b3sum, algorithm, root],
                         stdout=subprocess.PIPE, text=True)
    print(run.stdout, end="")
    run.check_returncode()
    return run.stdout.rsplit("tree CID ", 1)[1].strip()


def main() -> None:
    if len(sys.argv) != 2:
        raise SystemExit("usage: git_filesystem_native.py /path/to/b3sum")
    with tempfile.TemporaryDirectory(prefix="git-filesystem-") as path:
        results = []
        for algorithm in ("sha1", "sha256"):
            directory = Path(path) / algorithm
            directory.mkdir()
            results.append(run_fixture(directory, algorithm, Path(sys.argv[1]).resolve()))
        if results[0] != results[1]:
            raise RuntimeError("same Git filesystem yielded different target CIDs")
        print(f"SHA-1 and SHA-256 Git trees share the same BDASL mount CID: {results[0]}")


if __name__ == "__main__":
    main()
