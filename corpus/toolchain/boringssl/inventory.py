"""Record the entire installed package set and non-dpkg Go tool tree."""
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys

out = Path(sys.argv[1])
packages = subprocess.check_output(['dpkg-query', '-W', '-f=${binary:Package}\t${Version}\n'])
(out / 'lock.txt').write_bytes(packages)
tools = {}
names = ['cmake', 'ninja', 'go', 'perl', 'python3', 'qemu-aarch64']
names += [prefix + tool for prefix in ['', 'aarch64-linux-gnu-']
          for tool in ['gcc', 'g++', 'ld', 'ar', 'strip', 'readelf', 'objdump']]
for name in names:
    path = Path(shutil.which(name)).resolve()
    command = [name, 'version'] if name == 'go' else [name, '--version']
    if name == 'perl':
        command = [name, '-e', 'print $^V']
    tools[name] = {'path': str(path), 'sha256': hashlib.sha256(path.read_bytes()).hexdigest(),
                   'version': subprocess.check_output(command, text=True).strip().splitlines()[0]}
manifest = ''.join(f'{hashlib.sha256(p.read_bytes()).hexdigest()}  {p.relative_to("/usr/local/go")}\n'
                   for p in sorted(Path('/usr/local/go').rglob('*')) if p.is_file())
(out / 'go-tree.sha256').write_text(manifest)
(out / 'tools.json').write_text(json.dumps({'tools': tools, 'go': {
    'archive': 'https://go.dev/dl/go1.27.4.linux-amd64.tar.gz',
    'archive_sha256': '7226736c2339719cda28fbf3a54d71aa63bcefe376e98cef00034268dab24840',
    'archive_size': 70680823, 'tree_manifest_sha256': hashlib.sha256(manifest.encode()).hexdigest()},
    'package_lock_sha256': hashlib.sha256(packages).hexdigest()}, indent=2) + '\n')
