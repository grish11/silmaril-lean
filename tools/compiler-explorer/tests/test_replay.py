#!/usr/bin/env python3
"""Compare the driver to the pinned stock checker on temporary kernel fixtures."""
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

DRIVER = Path(__file__).resolve().parents[1] / "Replay.lean"


class KernelReplayTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.lean = shutil.which("lean")
        if not cls.lean:
            raise RuntimeError("run with the pinned Lean toolchain, e.g. lake env python3")
        prefix = subprocess.check_output([cls.lean, "--print-prefix"], text=True).strip()
        cls.checker = str(Path(prefix) / "bin" / "leanchecker")

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.env = {**os.environ, "LEAN_PATH": str(self.root), "LEAN_NUM_THREADS": "2"}
        self.env.pop("SILMARIL_REPLAY_MODULE", None)
        self.env.pop("SILMARIL_REPLAY_TARGETS", None)
        self.build("Group", "module\n@[expose] public section\ntheorem good : True := True.intro\n")
        self.build("Group.Child", "module\npublic import Group\n"
                   "@[expose] public section\ntheorem child : True := good\n")

    def call(self, args, env=None):
        return subprocess.run(args, env=env or self.env, cwd=self.root,
                              text=True, capture_output=True, timeout=60)

    def build(self, name, text):
        path = self.root.joinpath(*name.split(".")).with_suffix(".lean")
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)
        result = self.call([self.lean, "-DwarningAsError=true", "-o",
                            str(path.with_suffix(".olean")), str(path)])
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def driver(self, **mode):
        return self.call([self.lean, "-DwarningAsError=true", str(DRIVER)],
                         {**self.env, **mode})

    def test_target_and_descendant_selection_matches_stock(self):
        stock = self.call([self.checker, "--verbose", "Group", "Group.Child"])
        self.assertEqual(stock.returncode, 0, stock.stdout + stock.stderr)
        expected = {line.removeprefix("replaying ") for line in stock.stdout.splitlines()
                    if line.startswith("replaying ")}
        selected = self.driver(SILMARIL_REPLAY_TARGETS="Group Group.Child")
        self.assertEqual(selected.returncode, 0, selected.stdout + selected.stderr)
        names = selected.stdout.splitlines()
        self.assertEqual(set(names), {"Group", "Group.Child"})
        self.assertEqual(set(names), expected)
        self.assertEqual(len(names), len(set(names)))
        for name in names:
            result = self.driver(SILMARIL_REPLAY_MODULE=name)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_unknown_and_corrupt_modules_fail_closed(self):
        (self.root / "Corrupt.olean").write_bytes(b"not an olean")
        for name in ("Unknown", "Corrupt"):
            stock = self.call([self.checker, name])
            replay = self.driver(SILMARIL_REPLAY_MODULE=name)
            self.assertNotEqual(stock.returncode, 0)
            self.assertNotEqual(replay.returncode, 0)
            self.assertNotIn(": ok", replay.stdout)
        selected = self.driver(SILMARIL_REPLAY_TARGETS="Group Unknown")
        self.assertNotEqual(selected.returncode, 0)
        empty = self.driver(SILMARIL_REPLAY_TARGETS="")
        self.assertNotEqual(empty.returncode, 0)

    def test_malformed_proof_rejected_by_both_kernels(self):
        # Deliberately bypass declaration checking ONLY to manufacture a negative
        # fixture in a temporary directory; neither replay may accept this proof.
        self.build("Bad", '''import Lean
open Lean Elab Command in
run_cmd do
  let decl := Declaration.thmDecl {
    name := `badReplayFixture
    levelParams := []
    type := mkConst ``False
    value := mkConst ``True.intro
  }
  match (← getEnv).addDeclCore 0 1000 decl none false with
  | .ok env => setEnv env
  | .error e => throwError "{e.toMessageData {}}"
''')
        for result in (self.call([self.checker, "Bad"]),
                       self.driver(SILMARIL_REPLAY_MODULE="Bad")):
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("declaration type mismatch", result.stdout + result.stderr)
            self.assertNotIn(": ok", result.stdout)
        # Stock normal mode loads imports, without replaying their declarations.
        self.build("LoadsBad", "import Bad\ntheorem stillTrue : True := True.intro\n")
        for result in (self.call([self.checker, "LoadsBad"]),
                       self.driver(SILMARIL_REPLAY_MODULE="LoadsBad")):
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)


if __name__ == "__main__":
    unittest.main()
