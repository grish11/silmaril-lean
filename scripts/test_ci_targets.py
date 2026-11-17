import contextlib
import importlib.util
import io
import subprocess
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
spec = importlib.util.spec_from_file_location("ci_targets", HERE / "ci-targets.py")
ci = importlib.util.module_from_spec(spec)
spec.loader.exec_module(ci)

LIBS = ci.library_modules(ROOT / "lakefile.toml")
# The full list main pushes build: `make -s scope` without BASE.
FULL = subprocess.run(["make", "-s", "-C", str(ROOT), "scope"], check=True,
                      capture_output=True, text=True).stdout.split()
# The scoped targets of #942 (run 44036383254), which overflowed the prove client.
PR942 = (HERE / "testdata" / "ci-targets-942.txt").read_text().split()


def padded(n):
    """Targets whose encoded argv element is exactly n characters."""
    base = ["Silmaril"]
    pad = n - ci.encoded_length(base) - 1
    return base + ["x" * pad] if pad > 0 else base


class ChooseTests(unittest.TestCase):
    def test_full_is_main_list(self):
        self.assertIn("Silmaril", FULL)
        self.assertIn("wasm-opt", FULL)
        self.assertTrue(ci.fits(FULL))

    def test_below_and_at_threshold_keep_scoped(self):
        for n in (100, ci.LIMIT - ci.HEADROOM - 1, ci.LIMIT - ci.HEADROOM):
            t = padded(n)
            self.assertEqual(ci.encoded_length(t), max(n, ci.encoded_length(["Silmaril"])))
            self.assertEqual(ci.choose(t, FULL, LIBS)[0], t)

    def test_above_threshold_falls_back(self):
        t = ["+Silmaril.Wasm.Types"] * 400
        self.assertGreater(ci.encoded_length(t), ci.LIMIT - ci.HEADROOM)
        self.assertEqual(ci.choose(t, FULL, LIBS)[0], FULL)

    def test_pr942(self):
        self.assertEqual(len(PR942), 108)
        self.assertGreater(ci.encoded_length(PR942), ci.LIMIT)
        self.assertEqual(ci.uncovered(PR942, FULL, LIBS), [])
        targets, reason = ci.choose(PR942, FULL, LIBS)
        self.assertEqual(targets, FULL)
        self.assertIn("#752", reason)

    def test_uncovered_fails(self):
        t = PR942 + ["+NoSuchLibrary.Module", "no-such-exe"]
        self.assertEqual(ci.uncovered(t, FULL, LIBS), ["+NoSuchLibrary.Module", "no-such-exe"])
        with self.assertRaises(ci.TargetError):
            ci.choose(t, FULL, LIBS)

    def test_full_too_long_fails(self):
        with self.assertRaises(ci.TargetError):
            ci.choose(PR942, PR942, LIBS)

    def test_utf8_bytes_counted(self):
        self.assertEqual(ci.encoded_length(["é"]), len(ci.PREFIX) + 2)

    def test_globs(self):
        self.assertTrue(ci.glob_matches("A.+", "A.B"))
        self.assertFalse(ci.glob_matches("A.+", "A"))
        self.assertTrue(ci.glob_matches("A.*", "A"))
        self.assertTrue(ci.glob_matches("A.*", "A.B.C"))
        self.assertFalse(ci.glob_matches("A.*", "AB"))
        self.assertFalse(ci.glob_matches("A", "A.B"))

    def test_main_cli(self):
        err = io.StringIO()
        out = io.StringIO()
        with contextlib.redirect_stderr(err), contextlib.redirect_stdout(out):
            rc = ci.main(["--scoped", " ".join(PR942), "--full", " ".join(FULL)])
        self.assertEqual(rc, 0)
        self.assertEqual(out.getvalue().split(), FULL)
        self.assertIn("#752", err.getvalue())


if __name__ == "__main__":
    unittest.main()
