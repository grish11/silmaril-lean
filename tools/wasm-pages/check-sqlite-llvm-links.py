"""Generate and check real SQLite LLVM receipt controls for the Explorer browser test."""

import argparse
from copy import deepcopy
import json
from pathlib import Path
import subprocess
from tempfile import TemporaryDirectory


ROOT = Path(__file__).resolve().parents[2]
RECEIPT = Path("tools/sqlite-wasm/llvm-provenance/receipt.json")


def check(generator, reactor, output):
    receipt = json.loads((ROOT / RECEIPT).read_text())
    digest = receipt["stages"]["sqlite3.wasm"]["sha256"]
    module = f"sqlite.wasi.preview1.reactor.{digest}.json"
    symbols = {str(row["wasmSlot"]): row["symbol"] for row in receipt["symbols"]}
    cases = [
        ("default", None, None),
        ("matched", receipt, symbols),
        ("absent", None, {}),
    ]
    wrong_digest = deepcopy(receipt)
    wrong_digest["stages"]["sqlite3.wasm"]["sha256"] = "0" * 64
    cases.append(("wrong-digest", wrong_digest, {}))
    moved_slot = deepcopy(receipt)
    next(row for row in moved_slot["symbols"] if row["wasmSlot"] == 530)["wasmSlot"] = 529
    cases.append(("moved-slot", moved_slot, {k: v for k, v in symbols.items() if k != "530"}))
    for mode, keys in (
        ("bad-export-offset", ("codeOffset",)),
        ("bad-export-length", ("codeBytes",)),
        ("bad-export-span", ("codeOffset", "codeBytes")),
    ):
        bad = deepcopy(receipt)
        getter = next(row for row in bad["symbols"] if row["wasmSlot"] == 289)
        for key in keys:
            getter[key] += 1
        cases.append((mode, bad, {k: v for k, v in symbols.items() if k != "289"}))

    with TemporaryDirectory(prefix="wasm-pages-receipt-") as tmp:
        # This copy-on-write repository view leaves the real receipt and registry untouched.
        source, stage = ROOT, Path(tmp)
        for component in RECEIPT.parts:
            stage.mkdir(exist_ok=True)
            for entry in source.iterdir():
                if entry.name != component:
                    (stage / entry.name).symlink_to(entry)
            source, stage = source / component, stage / component
        artifacts = Path(tmp) / "silmaril/artifacts.toml"
        for mode, input_receipt, expected in cases:
            site = output / mode
            if site.exists():
                raise ValueError(f"use a fresh output directory: {site}")
            if input_receipt is None:
                stage.unlink(missing_ok=True)
            else:
                stage.write_text(json.dumps(input_receipt))
            cmd = [generator, artifacts, site]
            if expected is not None:
                cmd += ["--sqlite-reactor", reactor]
            print(mode, flush=True)
            subprocess.run(cmd, check=True, timeout=75)
            path = site / "wasm/m" / module
            if expected is None:
                if path.exists():
                    raise ValueError("default output contains the opt-in reactor")
                continue
            content = json.loads(path.read_text()).get("llvmReceipt")
            actual = content["symbols"] if content else {}
            if actual != expected:
                raise ValueError(f"{mode}: expected {expected}, got {actual}")
            print(f"{mode}: {len(actual)} links verified", flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("generator", "reactor", "output"):
        parser.add_argument(name, type=lambda value: Path(value).resolve())
    check(**vars(parser.parse_args()))
