"""The replay driver preserves every target and fails closed on checker failure."""
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
TARGETS = [
    'Silmaril.Proofs.Compiler.CompilesTo.Sim.Compose',
    'Silmaril.Proofs.Compiler.Explorer.Basic',
    'Silmaril.Proofs.Compiler.Explorer.Det',
    'Silmaril.Compiler.Explorer.Decompiled.Thms',
    'Silmaril.Proofs.Project.Shapes.CompilesTo.Explorer',
    'CompilesToExamples.Explorer.Builds',
    'CompilesToExamples.Explorer.Code',
    'CompilesToExamples.Explorer.Decompiled',
    'CompilesToExamples.Explorer.Rows',
]


class KernelReplay(unittest.TestCase):
    def run_driver(self, exit_code):
        with tempfile.TemporaryDirectory() as tmp:
            directory = Path(tmp)
            lake = directory / 'lake'
            lake.write_text('''#!/usr/bin/env python3
import os,subprocess,sys
from pathlib import Path
if sys.argv[1:] == ['env','which','lean']:
    print(Path(__file__).with_name('lean'))
else:
    raise SystemExit(subprocess.run(sys.argv[2:]).returncode)
''')
            checker = directory / 'leanchecker'
            checker.write_text('''#!/usr/bin/env python3
import json,os,sys
from pathlib import Path
assert os.environ['LEAN_NUM_THREADS'] == '2'
Path(os.environ['REPLAY_TRACE']).write_text(json.dumps(sys.argv[1:]))
raise SystemExit(int(os.environ['REPLAY_EXIT']))
''')
            lake.chmod(0o755)
            checker.chmod(0o755)
            trace = directory / 'trace.json'
            result = subprocess.run(['bash', 'tools/compiler-explorer/replay.sh'], cwd=ROOT,
                env={**{k:v for k,v in os.environ.items() if k != 'LEAN_NUM_THREADS'},
                     'LAKE': str(lake), 'REPLAY_TRACE': str(trace), 'REPLAY_EXIT': str(exit_code)},
                capture_output=True, text=True)
            return result, json.loads(trace.read_text())

    def test_all_targets_in_one_invocation(self):
        result, arguments = self.run_driver(0)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(arguments, ['--verbose', *TARGETS])
        for target in TARGETS:
            self.assertIn(f'leanchecker {target}: ok (batched)', result.stdout)
        self.assertIn('9 targets', result.stdout)

    def test_checker_failure_is_not_reported_as_success(self):
        result, arguments = self.run_driver(42)
        self.assertEqual(result.returncode, 42)
        self.assertEqual(arguments, ['--verbose', *TARGETS])
        self.assertNotIn(': ok', result.stdout)
        self.assertNotIn('leanchecker batch:', result.stdout)


if __name__ == '__main__':
    unittest.main()
