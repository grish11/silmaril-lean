#!/usr/bin/env python3
"""Measure one pipeline stage; write one immutable JSON receipt per invocation.

Usage: measure.py --stage NAME --output DIR [--input FILE ...] -- COMMAND ...
Run stages separately; do not label an aggregate build as kernel checking.
"""
import argparse
import datetime
import hashlib
import json
import os
from pathlib import Path
import platform
import socket
import subprocess
import sys
import time
import uuid


def sha(path):
    with open(path, 'rb') as f:
        return hashlib.file_digest(f, 'sha256').hexdigest()


def revision():
    def git(*args):
        return subprocess.check_output(['git', *args], text=True).strip()
    return {'commit': git('rev-parse', 'HEAD'),
            'dirty': bool(git('status', '--porcelain')),
            'diff_sha256': hashlib.sha256(subprocess.check_output(['git', 'diff', 'HEAD'])).hexdigest()}


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--stage', required=True)
    p.add_argument('--output', type=Path, required=True)
    p.add_argument('--input', action='append', default=[])
    p.add_argument('--target', required=True)
    p.add_argument('--cache', choices=['cold', 'warm', 'unspecified'], default='unspecified')
    p.add_argument('--concurrency', type=int, default=1)
    p.add_argument('--repository-receipt', type=Path,
                   help='JSON revision/dirty/diff_sha256 from the host when Git is unavailable in a pinned container')
    p.add_argument('command', nargs=argparse.REMAINDER)
    a = p.parse_args()
    command = a.command[1:] if a.command[:1] == ['--'] else a.command
    if not command or not 1 <= a.concurrency <= 8:
        p.error('a command and concurrency in 1..8 are required')
    run = str(uuid.uuid4())
    record = {'schema_version': 1, 'run_id': run, 'stage': a.stage,
              'measurement_tool_sha256': sha(__file__),
              'started_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
              'command': command, 'cwd': str(Path.cwd()), 'target': a.target,
              'repository': json.loads(a.repository_receipt.read_text()) if a.repository_receipt else revision(),
              'cache': a.cache, 'concurrency': a.concurrency,
              'lean_toolchain': Path('lean-toolchain').read_text().strip() if Path('lean-toolchain').exists() else None,
              'runner': {'hostname': socket.gethostname(), 'platform': platform.platform(),
                         'cpu_model': next((l.split(':', 1)[1].strip() for l in Path('/proc/cpuinfo').read_text().splitlines() if l.startswith('model name')), None),
                         'visible_cpus': os.cpu_count(), 'task_cpu_budget': 8,
                         'task_memory_budget_bytes': 32 * 1024**3},
              'inputs': [{'path': f, 'sha256': sha(f)} for f in a.input]}
    record['runner']['cgroup'] = {name: Path('/sys/fs/cgroup', name).read_text().strip()
                                 for name in ['cpu.max', 'memory.max'] if Path('/sys/fs/cgroup', name).exists()}
    start = time.monotonic()
    child = subprocess.Popen(command)
    _, status, usage = os.wait4(child.pid, 0)
    child.returncode = os.waitstatus_to_exitcode(status)
    record.update(wall_seconds=time.monotonic() - start, exit_code=child.returncode,
                  user_cpu_seconds=usage.ru_utime, system_cpu_seconds=usage.ru_stime,
                  peak_rss_kib=usage.ru_maxrss,
                  measurement='Linux wait4 child accounting; includes waited-for descendants; RSS is maximum, not sum')
    a.output.mkdir(parents=True, exist_ok=True)
    with (a.output / f'{run}.json').open('x') as f:
        json.dump(record, f, indent=2)
        f.write('\n')
    print(f'measurement: {a.output / (run + ".json")}', file=sys.stderr, flush=True)
    return child.returncode if child.returncode >= 0 else 128 - child.returncode


if __name__ == '__main__':
    raise SystemExit(main())
