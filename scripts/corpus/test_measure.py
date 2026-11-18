"""Exercise exit propagation and non-clobbering stage receipts."""
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest


class StageReceipts(unittest.TestCase):
    def test_receipts_and_failures(self):
        with tempfile.TemporaryDirectory() as d:
            for status in (0, 7):
                r = subprocess.run([sys.executable, str(Path(__file__).with_name('measure.py')),
                                    '--stage', 'test', '--output', d, '--target', 'host', '--',
                                    sys.executable, '-c', f'raise SystemExit({status})'], capture_output=True)
                self.assertEqual(r.returncode, status)
            receipts = [json.loads(p.read_text()) for p in Path(d).glob('*.json')]
            self.assertEqual(len(receipts), 2)
            self.assertEqual({r['exit_code'] for r in receipts}, {0, 7})
            self.assertEqual(len({r['run_id'] for r in receipts}), 2)
            self.assertTrue(all(r['wall_seconds'] > 0 for r in receipts))
            self.assertTrue(all(r['peak_rss_kib'] > 0 for r in receipts))


if __name__ == '__main__':
    unittest.main()
