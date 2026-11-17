"""The GCC torture manifest and stored TV report invariants (scripts/c-tv/check-torture.py), in the
CI helpers job: no GCC checkout, compiler or native run is needed."""
import os
import subprocess
import sys
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))


CHECK = os.path.join(HERE, "c-tv", "check-torture.py")
REPORT = os.path.join(os.path.dirname(HERE), "benchmarks", "gcc-torture", "tv-report.json.gz")


def check(*args):
    return subprocess.run([sys.executable, "-I", CHECK, *args], capture_output=True, text=True)


class TortureInvariants(unittest.TestCase):
    def test_manifest_and_report(self):
        p = check()
        self.assertEqual(p.returncode, 0, p.stdout + p.stderr)

    def test_tampered_reports_are_rejected(self):
        import gzip, json, tempfile
        base = json.load(gzip.open(REPORT))
        tamper = {
            "drop a row": lambda j: j["cases"].pop(),
            "duplicate a case": lambda j: j["cases"].insert(1, j["cases"][0]),
            "fake cross-validation": lambda j: j["cases"][5].update(status="cross-validated"),
            "wrong source hash": lambda j: j["cases"][5].update(sha256="0" * 64),
            "inflated summary": lambda j: j["summary"].update({"cross-validated": j["summary"]["cross-validated"] + 1}),
            "unpinned profile": lambda j: j["options"].pop("pipeline"),
            "unknown status": lambda j: j["cases"][5].update(status="validated"),
            "unknown flag": lambda j: j["cases"][5].update(coverage=True),
        }
        with tempfile.TemporaryDirectory() as d:
            for name, f in tamper.items():
                j = json.loads(json.dumps(base))
                f(j)
                path = os.path.join(d, "r.json.gz")
                with gzip.open(path, "wb") as out:
                    out.write(json.dumps(j).encode())
                self.assertNotEqual(check("--report", path).returncode, 0, name)


if __name__ == "__main__":
    unittest.main()
