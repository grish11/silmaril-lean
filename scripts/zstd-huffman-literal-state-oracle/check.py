#!/usr/bin/env python3
"""Compare Lean literal table state with the pinned libzstd same-frame pair."""
import argparse
from hashlib import sha256
from io import BytesIO
import json
from pathlib import Path
import subprocess
from tempfile import TemporaryDirectory

PIN = "f8745da6ff1ad1e7bab384bd1f9d742439278e99"
FRAME_HASH = "6fb53d7c3100b6c9c30c275f3c7bb02fba4fd5ebb8dd96bcc4078ade9f24d73e"
SIZE = 135168
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]


def run(*args, data=None):
    return subprocess.check_output(args, cwd=ROOT, input=data)


def require(ok, reason):
    if not ok:
        raise SystemExit(reason)


def digest(data):
    return sha256(data).hexdigest()


def check_lean(work, frame, blocks, outputs):
    paths = []
    for block in blocks:
        start = block["block_header_offset"] + 3
        body = frame[start:start + block["block_body_bytes"]]
        path = work / f'block-{block["block_index"]}.bin'
        path.write_bytes(body)
        paths.append(path)

    caps = [str(block[key]) for block in blocks for key in ("section_bytes", "regenerated_bytes")]
    observed = run("lake", "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true", "--run",
                   HERE / "Interop.lean", *paths, work, *caps)
    for label, block, raw in zip(("new-tree", "treeless", "interposed"),
                                 (*blocks, blocks[1]), observed.splitlines(), strict=True):
        used, count = map(int, raw.split())
        require((used, count) == (block["section_bytes"], block["regenerated_bytes"]),
                f"{label}: wrong extent or regenerated size")
        expected = outputs["new-tree" if label == "new-tree" else "treeless"]
        require((work / f"{label}.literals").read_bytes() == expected, f"{label}: literal bytes differ")
        suffix = (work / f"{label}.suffix").read_bytes()
        require(suffix == paths[block["block_index"] - 1].read_bytes()[used:],
                f"{label}: following bytes changed")
    print("Lean matched the native pair and raw/RLE interposition, and rejected reset and one-less caps")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--zstd-source", type=Path, help="optional clean checkout at the pinned SHA")
    parser.add_argument("--out", type=Path, help="write the frame, literals, and verification manifest")
    args = parser.parse_args()

    entropy = b"".join(sha256(i.to_bytes(4, "little")).digest() for i in range(SIZE // 32))
    original = bytes(byte % 5 for byte in entropy)
    with TemporaryDirectory(prefix="silmaril-zstd-table-fixture-") as directory:
        work = Path(directory)
        source = args.zstd_source.resolve() if args.zstd_source else None
        if source is None:
            source = work / "zstd"
            run("git", "init", "-q", source)
            run("git", "-C", source, "fetch", "-q", "--depth=1", "https://github.com/facebook/zstd.git", PIN)
            run("git", "-C", source, "checkout", "-q", "--detach", "FETCH_HEAD")
        require(run("git", "-C", source, "rev-parse", "HEAD").decode().strip() == PIN, "wrong libzstd SHA")
        require(run("git", "-C", source, "diff", "HEAD", "--") == b"", "modified libzstd sources")
        library = source / "lib"
        run("make", "-C", library, "-j2", "libzstd.a")
        executable = work / "reference"
        run("cc", "-std=c11", "-Wall", "-Wextra", "-Werror", "-O2", "-I", library,
            Path(__file__).with_name("reference.c"), library / "libzstd.a", "-o", executable)

        frame = run(executable, "compress", data=original)
        require(digest(frame) == FRAME_HASH, "unexpected frame digest")
        require(run(executable, "decode", data=frame) == original, "native full-frame decode differs")
        observed = BytesIO(run(executable, "pair", data=frame))
        frame_header, dictionary, maximum = map(int, observed.readline().split())

        metadata = {"libzstd_commit": PIN, "compression_level": 3, "input_bytes": len(original),
                    "input_sha256": digest(original), "frame_bytes": len(frame), "frame_sha256": digest(frame),
                    "frame_header_bytes": frame_header, "dictionary_id": dictionary,
                    "block_maximum": maximum, "blocks": []}
        files = {"same-frame.zst": frame}
        outputs = {}
        for index, label in enumerate(("new-tree", "treeless"), 1):
            offset, block_size, kind, fmt, used, count = map(int, observed.readline().split())
            literals = observed.read(count)
            require(len(literals) == count, "native literal output is incomplete")
            body_at = offset + 3
            section = frame[body_at:body_at + used]
            suffix = frame[body_at + used:body_at + block_size]
            width = (3, 3, 4, 5)[fmt]
            details = {"block_index": index, "block_header_offset": offset, "block_body_bytes": block_size,
                       "literal_kind": kind, "size_format": fmt, "header_bytes": width,
                       "section_bytes": used, "section_sha256": digest(section),
                       "regenerated_bytes": count, "literals_sha256": digest(literals),
                       "following_bytes": len(suffix), "following_sha256": digest(suffix)}
            if kind == 2:
                details["tree_encoding"] = "direct" if section[width] >= 128 else "fse"
            metadata["blocks"].append(details)
            files[f"{label}.section.bin"] = section
            files[f"{label}.literals.bin"] = literals
            outputs[label] = literals
        require(observed.read() == b"reset=dictionary_corrupted raw-rle=preserved\n", "native state controls")
        metadata["treeless_after_reset"] = "ZSTD_error_dictionary_corrupted"
        metadata["raw_and_rle_between_pair"] = "second output unchanged"
        pinned_manifest = Path(__file__).with_name("fixture.json")
        require(metadata == json.loads(pinned_manifest.read_text()), "fixture manifest differs")
        rendered = json.dumps(metadata, indent=2) + "\n"
        check_lean(work, frame, metadata["blocks"], outputs)
        if args.out:
            args.out.mkdir(parents=True, exist_ok=True)
            for name, data in files.items():
                (args.out / name).write_bytes(data)
            (args.out / "fixture.json").write_text(rendered)
        print(rendered, end="")


if __name__ == "__main__":
    main()
