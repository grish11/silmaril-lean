#!/usr/bin/env python3
"""Start a corpus command in its own session, with durable logs and PID evidence.

Launch success is not command completion. Inspect the command's own receipts.
Only the explicit command is recorded; inherited environment values are omitted.
"""
import argparse
import datetime
import hashlib
import json
import os
from pathlib import Path
import subprocess


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--record', type=Path, required=True)
    p.add_argument('--log', type=Path, required=True)
    p.add_argument('command', nargs=argparse.REMAINDER)
    a = p.parse_args()
    command = a.command[1:] if a.command[:1] == ['--'] else a.command
    if not command:
        p.error('an explicit command is required')
    # All host descendants share two CPUs, leaving the two 3-CPU workers within
    # the aggregate 8-CPU budget. This changes only this process and descendants.
    cpus = sorted(os.sched_getaffinity(0))[:2]
    os.sched_setaffinity(0, cpus)
    with a.record.open('x') as record, a.log.open('xb') as log:
        child = subprocess.Popen(command, stdin=subprocess.DEVNULL, stdout=log,
            stderr=subprocess.STDOUT, start_new_session=True, close_fds=True)
        data = {'pid': child.pid, 'session_id': os.getsid(child.pid),
                'started_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
                'cwd': str(Path.cwd()), 'command': command, 'log': str(a.log.resolve()),
                'host_allowed_cpus': cpus, 'launcher_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                'status': 'launched; completion must be established from command receipts'}
        json.dump(data, record, indent=2)
        record.write('\n')
    print(f'launched PID {child.pid}, session {data["session_id"]}; record {a.record}')


if __name__ == '__main__':
    main()
