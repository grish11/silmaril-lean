import json
from pathlib import Path
import subprocess
import sys
import tempfile
import time
import unittest


class DetachedCommand(unittest.TestCase):
    def test_child_outlives_launcher_in_its_own_session_and_obeys_host_cpu_cap(self):
        launcher = Path(__file__).with_name('background.py')
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            child = ('import json,os,time; from pathlib import Path; time.sleep(0.2); '
                     'Path("done.json").write_text(json.dumps({"pid":os.getpid(),"sid":os.getsid(0),'
                     '"ppid":os.getppid(),"cpus":list(os.sched_getaffinity(0))})); print("done",flush=True)')
            result = subprocess.run([sys.executable, str(launcher), '--record', 'job.json',
                                     '--log', 'job.log', '--', sys.executable, '-c', child],
                                    cwd=root, capture_output=True, text=True, check=True)
            for _ in range(100):
                if (root / 'done.json').exists():
                    break
                time.sleep(0.02)
            evidence = json.loads((root / 'done.json').read_text())
            record = json.loads((root / 'job.json').read_text())
            self.assertEqual(evidence['pid'], evidence['sid'])
            self.assertEqual(evidence['pid'], record['pid'])
            self.assertLessEqual(len(evidence['cpus']), 2)
            self.assertEqual((root / 'job.log').read_text(), 'done\n')
            again = subprocess.run([sys.executable, str(launcher), '--record', 'job.json',
                                    '--log', 'job.log', '--', 'false'], cwd=root, capture_output=True)
            self.assertNotEqual(again.returncode, 0)


if __name__ == '__main__':
    unittest.main()
