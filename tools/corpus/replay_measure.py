"""Linux child-process measurements with CPU affinity and a sampled RSS guard.

The RSS guard observes only this child's process group; it is not cgroup isolation.
Shared pages may be counted more than once. No host/kernel setting is changed.
"""
from pathlib import Path
import hashlib
import os
import resource
import signal
import subprocess
import threading
import time


def measure(command, *, stdout, stderr, cpus=8, memory_gib=32, env=None):
    allowed=sorted(os.sched_getaffinity(0))[:cpus]
    if len(allowed)!=cpus: raise ValueError('insufficient CPUs for affinity')
    page_kib=os.sysconf('SC_PAGE_SIZE')//1024
    stop=threading.Event()
    sampled={'peak_tree_rss_kib':0,'peak_process_virtual_kib':0,'rss_guard_triggered':False,'sample_seconds':0.05}
    def child_setup():
        os.setsid()
        os.sched_setaffinity(0,allowed)
        # Lean's allocator may reserve large virtual arenas; virtual size is not
        # physical memory. The guard below observes RSS instead of RLIMIT_AS.
    def observe(pid):
        pending=[pid];seen=set();rss=0
        while pending:
            p=pending.pop()
            if p in seen: continue
            seen.add(p)
            try:
                fields=Path(f'/proc/{p}/statm').read_text().split()
                rss+=int(fields[1])*page_kib
                sampled['peak_process_virtual_kib']=max(sampled['peak_process_virtual_kib'],int(fields[0])*page_kib)
                for task in Path(f'/proc/{p}/task').iterdir():
                    try: pending.extend(int(c) for c in (task/'children').read_text().split())
                    except FileNotFoundError: pass
            except (FileNotFoundError,ProcessLookupError): pass
        return rss
    with stdout.open('wb') as out,stderr.open('wb') as err:
        began=time.monotonic()
        process=subprocess.Popen(command,stdout=out,stderr=err,env=env,preexec_fn=child_setup)
        def sample():
            while not stop.is_set():
                rss=observe(process.pid)
                sampled['peak_tree_rss_kib']=max(sampled['peak_tree_rss_kib'],rss)
                if rss>memory_gib*1024**2:
                    sampled['rss_guard_triggered']=True
                    try: os.killpg(process.pid,signal.SIGKILL)
                    except ProcessLookupError: pass
                    return
                stop.wait(sampled['sample_seconds'])
        watcher=threading.Thread(target=sample,daemon=True);watcher.start()
        try:
            _,status,usage=os.wait4(process.pid,0)
            process.returncode=os.waitstatus_to_exitcode(status)
        finally:
            stop.set();watcher.join()
        elapsed=time.monotonic()-began
    sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
    return {'argv':command,'wall_seconds':elapsed,'exit':process.returncode,
            'stdout_sha256':sha(stdout),'stderr_sha256':sha(stderr),
            'stdout_bytes':stdout.stat().st_size,'stderr_bytes':stderr.stat().st_size,
            'resource':{'user_seconds':usage.ru_utime,'system_seconds':usage.ru_stime,
                        'max_rss_kib':usage.ru_maxrss,'major_faults':usage.ru_majflt,
                        'minor_faults':usage.ru_minflt,'voluntary_switches':usage.ru_nvcsw,
                        'involuntary_switches':usage.ru_nivcsw,**sampled,
                        'cpu_affinity':allowed,'rss_guard_gib':memory_gib,
                        'method':'wait4 plus sampled descendant RSS sum; not a cgroup/hard aggregate memory limit'}}
