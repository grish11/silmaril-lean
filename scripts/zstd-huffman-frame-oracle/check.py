#!/usr/bin/env python3
"""Compare the checked whole-frame Lean decoder against pinned libzstd."""
import argparse
from hashlib import sha256
import json
from runpy import run_path
from pathlib import Path
import subprocess
from tempfile import TemporaryDirectory

PIN = "f8745da6ff1ad1e7bab384bd1f9d742439278e99"
UNCHECKED = "6fb53d7c3100b6c9c30c275f3c7bb02fba4fd5ebb8dd96bcc4078ade9f24d73e"
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
WINDOW = 135168
COMMANDS = 27037
MAGIC = bytes.fromhex("28 b5 2f fd")
KIND = ("raw", "RLE", "compressed", "reserved")


def digest(data):
    return sha256(data).hexdigest()


def require(condition, what):
    if not condition:
        raise SystemExit(what)


def run(*args, data=None):
    return subprocess.check_output(args, input=data)


def block(kind, size, body, *, last=False):
    return ((size << 3) | (kind << 1) | last).to_bytes(3, "little") + body


def header(size, *, checksum=False):
    return MAGIC + bytes([0xa0 | (4 if checksum else 0)]) + size.to_bytes(4, "little")


def blocks(frame, position):
    """Record physical extents after the known fixture header."""
    require(frame[:4] == MAGIC, "fixture magic changed")
    while True:
        require(position + 3 <= len(frame), "incomplete fixture block header")
        word = int.from_bytes(frame[position:position + 3], "little")
        kind, size, last = (word >> 1) & 3, word >> 3, bool(word & 1)
        count = 1 if kind == 1 else size
        body = frame[position + 3:position + 3 + count]
        require(len(body) == count, "incomplete fixture block body")
        yield position, kind, size, body
        position += 3 + count
        if last:
            break
    require(len(frame) - position == (4 if frame[4] & 4 else 0), "wrong fixture trailer extent")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--zstd-source", type=Path, help="optional clean checkout at the pinned SHA")
    args = parser.parse_args()
    original = bytes(byte % 5 for i in range(WINDOW // 32) for byte in sha256(i.to_bytes(4, "little")).digest())

    with TemporaryDirectory(prefix="silmaril-zstd-huffman-frame-") as directory:
        work = Path(directory)
        zstd = args.zstd_source.resolve() if args.zstd_source else work / "zstd"
        if args.zstd_source is None:
            run("git", "init", "-q", zstd)
            run("git", "-C", zstd, "fetch", "-q", "--depth=1", "https://github.com/facebook/zstd.git", PIN)
            run("git", "-C", zstd, "checkout", "-q", "--detach", "FETCH_HEAD")
        require(run("git", "-C", zstd, "rev-parse", "HEAD").decode().strip() == PIN, "wrong libzstd SHA")
        require(run("git", "-C", zstd, "diff", "HEAD", "--") == b"", "modified libzstd")
        library = zstd / "lib"
        run("make", "-C", library, "-j2", "libzstd.a")
        native = work / "libzstd-reference"
        run("c++", "-std=c++17", "-O2", "-Wall", "-Wextra", "-Werror", "-I", library,
            ROOT / "scripts/zstd-literal-oracle/reference.cc", library / "libzstd.a", "-o", native)

        def ref(mode, data, cap=2 * WINDOW + 16):
            return run(native, mode, str(cap), data=data)

        def lean(frame, *, input_cap=None, output_cap=WINDOW + 8, window_cap=WINDOW + 8, commands=COMMANDS):
            encoded, decoded = work / "encoded", work / "lean-output"
            decoded.unlink(missing_ok=True)
            encoded.write_bytes(frame)
            cap = len(frame) if input_cap is None else input_cap
            command = ["lake", "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true", "--run",
                       HERE / "Interop.lean", encoded, decoded, str(cap), str(output_cap),
                       str(window_cap), str(commands)]
            result = subprocess.run(command, cwd=ROOT, capture_output=True, text=True)
            if result.returncode == 3:
                require(not decoded.exists(), "a rejecting decode wrote output")
                return result.stdout.strip()
            require(result.returncode == 0, result.stdout + result.stderr)
            return decoded.read_bytes()

        fixtures = {"libzstd_commit": PIN, "compression_level": 3, "cases": {}, "rejections": {}}

        def reject(name, frame, error, *, native_status="rejected", **caps):
            got = lean(frame, **caps)
            require(isinstance(got, str) and got.rstrip(")").endswith("." + error),
                    f"{name}: expected {error}, got {str(got)[:200]}")
            if native_status == "rejected":
                observed = subprocess.run([native, "decode", str(2 * WINDOW + 16)], input=frame, capture_output=True)
                require(observed.returncode == 3, f"{name}: libzstd unexpectedly accepted")
            fixtures["rejections"][name] = {"frame_sha256": digest(frame), "lean_error": error,
                                            "libzstd": native_status, "limits": caps}
            print(f"{name}: {error}; libzstd {native_status}")

        bare = ref("compress", original)
        checked = ref("compress-checksum", original)
        require(digest(bare) == UNCHECKED, "no-checksum pin changed")
        require(checked[4] == 0xa4 and checked[5:-4] == bare[5:] and checked[:4] == MAGIC,
                "native checksummed frame differs beyond the flag and checksum")
        ((first_at, _, n1, new_tree), (_, _, n2, treeless)) = list(blocks(checked, 9))
        require((n1, n2, new_tree[0] & 15, treeless[0] & 15) == (49308, 1560, 10, 3) and new_tree[4] >= 128,
                "expected four-stream new tree followed by single-stream treeless")
        interposed_body = (block(2, n1, new_tree) + block(0, 4, b"raw!") + block(1, 4, b"Y")
                           + block(2, n2, treeless, last=True))
        larger = WINDOW + 8
        interposed_plain = ref("decode", header(larger) + interposed_body)
        require(len(interposed_plain) == larger and interposed_plain[131072:131080] == b"raw!YYYY",
                "native decoder did not expand the interposed blocks")
        interposed = header(larger, checksum=True) + interposed_body + ref("compress-checksum", interposed_plain)[-4:]

        # Non-single-segment header with a 144 KiB window and no content size.
        undeclared = MAGIC + bytes([4, 0x39]) + checked[9:]
        fse_plain = bytes(145 + byte % 4 for i in range(32) for byte in sha256(i.to_bytes(4, "little")).digest())
        fse = ref("compress", fse_plain)
        fse_body = ref("first-block", fse)
        fse_header = len(fse) - 3 - len(fse_body)
        require(fse_body[0] & 15 == 2 and 0 < fse_body[3] < 128, "expected single-stream FSE weights")

        # Reuse the earlier strict-window differential with an explicit native comparison.
        common = run_path(str(ROOT / "scripts/zstd-literal-oracle/check_rle_frame.py"))
        frame, raw, rle, compressed, single = (
            common[name] for name in ("frame", "raw", "rle", "compressed", "single")
        )
        small_window = common["WINDOW"]
        seed = bytes(i % 251 for i in range(small_window))
        history = [raw(seed), rle(13, ord("x"))]
        near = frame(history + [compressed(native, b"", single(0, small_window + 2, 3))])
        equal = frame(history + [compressed(native, b"", single(0, small_window + 3, 3))])
        require(ref("decode", equal) == seed + b"x" * 13 + seed[13:16], "native equality fixture")

        for name, encoded, expected, window, header_size in (
            ("same-frame", bare, original, WINDOW, 9),
            ("same-frame-checksum", checked, original, WINDOW, 9),
            ("physical-raw-rle-between", interposed, interposed_plain, larger, 9),
            ("no-declared-content-size", undeclared, original, 147456, 6),
            ("new-tree-fse-weights", fse, fse_plain, len(fse_plain), fse_header),
            ("distance-one-below-window", near, seed + b"x" * 13 + seed[14:17], small_window, 6),
        ):
            require(ref("decode", encoded) == expected, f"{name}: native whole-frame output")
            require(lean(encoded, output_cap=len(expected), window_cap=window) == expected,
                    f"{name}: Lean whole-frame output")
            fixtures["cases"][name] = {
                "frame_bytes": len(encoded), "frame_sha256": digest(encoded), "window": window,
                "output_bytes": len(expected), "output_sha256": digest(expected),
                "checksum": encoded[-4:].hex() if encoded[4] & 4 else None,
                "blocks": [
                    {"header_offset": offset, "kind": KIND[kind], "size": size, "body_bytes": len(body),
                     "body_sha256": digest(body)}
                    for offset, kind, size, body in blocks(encoded, header_size)
                ],
            }
            print(f"{name}: Lean and libzstd matched {len(expected)} bytes, frame={digest(encoded)}")

        marker_at = first_at + 3 + n1 - 1
        require(checked[marker_at] != 0, "expected a sequence marker in the first block")
        reject("zero first sequence marker", checked[:marker_at] + b"\x00" + checked[marker_at + 1:], "badEndMarker")
        reject("missing checksum byte", checked[:-1], "truncated")
        reject("bad checksum", checked[:-1] + bytes([checked[-1] ^ 1]), "checksumMismatch")
        reject("wrong declared size", header(WINDOW + 1, checksum=True) + checked[9:], "contentSizeMismatch")
        reject("truncated compressed extent", bare[:-1], "truncated")
        reject("trailing byte", checked + b"\x00", "trailingInput")
        reject("nonzero dictionary ID", checked[:4] + b"\xa5\x07" + checked[5:], "unsupportedDictionary 7")
        reject("reserved block type", bare[:first_at] + bytes([bare[first_at] | 2]) + bare[first_at + 1:],
               "reservedBlock")
        reject("treeless after dictionary-free reset", header(4096) + block(2, n2, treeless, last=True),
               "unavailableTable")
        require(ref("decode", checked + checked) == original * 2, "native did not accept concatenation")
        reject("concatenated frames", checked + checked, "trailingInput", native_status="accepted")
        skippable = bytes.fromhex("50 2a 4d 18 00 00 00 00")
        require(ref("decode", skippable) == b"", "native did not accept skippable frame")
        reject("skippable frame", skippable, "skippableFrame", native_status="accepted")

        reject("distance-equal-to-window", equal, "offsetOutsideWindow", native_status="accepted",
               window_cap=small_window)
        for label, error, caps in (
            ("one-less input cap", "inputLimit", {"input_cap": len(checked) - 1}),
            ("one-less output cap", "outputLimit", {"output_cap": WINDOW - 1}),
            ("one-less window cap", "windowLimit", {"window_cap": WINDOW - 1}),
            ("one-less command cap", "sequenceLimit", {"commands": COMMANDS - 1}),
        ):
            reject(label, checked, error, native_status="not compared for caller cap", **caps)

        manifest = HERE / "fixtures.json"
        require(fixtures == json.loads(manifest.read_text()), "fixture manifest differs")


if __name__ == "__main__":
    main()
