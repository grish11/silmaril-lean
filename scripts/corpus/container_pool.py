"""Two isolated, persistent corpus workers; no per-profile container creation.

Only immutable recipes/cache and each worker's own output directory are mounted.
The root filesystem is read-only. All writable container state is reset between
profiles. This is workspace independence, not fresh-container independence.
"""
import datetime
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import uuid


RESET = ['bash', '-eu', '-c',
         'find /build /tmp /root /dev/shm -mindepth 1 -maxdepth 1 -exec rm -rf -- {} +; '
         'test -z "$(find /build /tmp /root /dev/shm -mindepth 1 -print -quit)"']
ENV = {'PATH': '/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin',
       'HOME': '/root', 'LC_ALL': 'C', 'TZ': 'UTC', 'SOURCE_DATE_EPOCH': '1762128000',
       'JOBS': '3'}


def sha(path):
    with Path(path).open('rb') as f:
        return hashlib.file_digest(f, 'sha256').hexdigest()


class ContainerPool:
    def __init__(self, image, recipes, cache, directory, toolchain="corpus/toolchain"):
        if not image.startswith('sha256:') or len(image) != 71:
            raise ValueError('pool requires an immutable Docker image ID')
        self.toolchain = toolchain
        self.image, self.recipes, self.cache = image, recipes, cache
        self.directory = directory
        self.directory.mkdir(parents=True, exist_ok=False)
        self.containers = []
        self.recovered = False
        self.profiles = 0
        self.record = {'toolchain': toolchain, 'pool_id': str(uuid.uuid4()), 'image_id': image,
                       'lifecycle': 'two independently initialized persistent containers; reused across profiles',
                       'isolation': 'read-only root; private /build, /tmp, /root tmpfs; separate writable output mounts',
                       'reset': RESET, 'environment': ENV,
                       'resources': {'containers': 2, 'cpu_per_container': 3,
                                     'memory_bytes_per_container': 12 * 1024**3,
                                     'execution': 'serial builds, strips and tests; no third container'},
                       'started_utc': self.now(), 'workers': [], 'profiles': []}

    @staticmethod
    def now():
        return datetime.datetime.now(datetime.timezone.utc).isoformat()

    def save(self):
        temporary = self.directory / 'lifecycle.json.tmp'
        temporary.write_text(json.dumps(self.record, indent=2) + '\n')
        temporary.replace(self.directory / 'lifecycle.json')

    @classmethod
    def reconnect(cls, directory, recipes, cache, image, controller, toolchain="corpus/toolchain"):
        """Attach only to two idle, unchanged workers; never initialize replacements.

        A supported recovery reruns all validation of two successfully measured
        builds. An incomplete build needs explicit operator recovery instead.
        """
        obj = cls.__new__(cls)
        obj.toolchain = toolchain
        obj.directory, obj.recipes, obj.cache, obj.image = directory, recipes, cache, image
        obj.record = json.loads((directory / 'lifecycle.json').read_text())
        if obj.record['image_id'] != image or 'stopped_utc' in obj.record or 'failure' in obj.record:
            raise ValueError('pool cannot be reconnected: changed image, stopped or failed')
        obj.containers = [w['container_id'] for w in obj.record['workers']]
        if len(obj.containers) != 2 or len(set(obj.containers)) != 2:
            raise ValueError('reconnect requires exactly two independent workers')
        if not obj.record['profiles'] or obj.record['profiles'][-1]['status'] != 'running':
            raise ValueError('reconnect requires an unpublished running profile')
        if obj.record.get('toolchain', 'corpus/toolchain') != toolchain:
            raise ValueError('reconnect toolchain identity differs')
        expected_lock = (recipes / toolchain / 'lock.txt').read_bytes()
        for slot, container in enumerate(obj.containers):
            actual = json.loads(subprocess.check_output(['docker', 'inspect', container], text=True))[0]
            limits = actual['HostConfig']
            if (not actual['State']['Running'] or actual['Image'] != image or
                not limits['ReadonlyRootfs'] or limits['Privileged'] or
                limits['NanoCpus'] != 3_000_000_000 or limits['Memory'] != 12 * 1024**3 or
                limits['PidsLimit'] != 256 or limits['NetworkMode'] != 'host' or
                limits.get('Tmpfs') != {'/build': 'rw,exec,size=8g', '/tmp': 'rw,exec,size=1g', '/root': 'rw,size=64m'}):
                raise ValueError(f'worker {slot}: runtime/image/limits/isolation changed')
            expected_mounts = {'/corpus': (str(recipes / 'corpus'), False),
                               '/scripts': (str(recipes / 'scripts'), False),
                               '/cache': (str(cache), False), '/out': (str(obj.output(slot)), True)}
            mounts = {m['Destination']: (m['Source'], m['RW']) for m in actual['Mounts'] if m['Type'] == 'bind'}
            if mounts != expected_mounts or len(actual['Mounts']) != len(expected_mounts):
                raise ValueError(f'worker {slot}: mounts changed')
            processes = subprocess.check_output(['docker', 'top', container, '-eo', 'pid,comm'], text=True).splitlines()
            if len(processes) != 2 or processes[1].split()[1:] != ['sleep']:
                raise ValueError(f'worker {slot}: not idle; refuse concurrent recovery')
            lock = obj.exec(slot, ['dpkg-query', '-W', '-f=${binary:Package}\t${Version}\n'], capture=True)
            if lock != expected_lock or (directory / f'packages-{slot}.txt').read_bytes() != expected_lock:
                raise ValueError(f'worker {slot}: whole installed package lock differs on reconnect')
            obj.verify_tools(slot)
        obj.profiles = len(obj.record['profiles'])
        obj.recovered = True
        obj.record.setdefault('controller_reconnections', []).append({
            'utc': obj.now(), 'profile': obj.record['profiles'][-1]['identity'],
            'reason': 'previous host controller ended; existing idle workers preserved',
            'validation': 'image, exact mounts, limits, isolation, idle processes and whole package locks rechecked',
            'strategy': 'verify two successful measured builds; rerun all stripping, runtime tests, receipts and census',
            'controller': controller})
        obj.save()
        return obj

    def output(self, slot):
        return self.directory / str(slot)

    def __enter__(self):
        if self.recovered:
            return self
        try:
            for slot in range(2):
                self.output(slot).mkdir()
                command = ['docker', 'run', '--network', 'host', '--pull=never', '--detach',
                           '--read-only', '--cpus', '3', '--memory', '12g', '--memory-swap', '12g',
                           '--pids-limit', '256', '--workdir', '/',
                           '--tmpfs', '/build:rw,exec,size=8g', '--tmpfs', '/tmp:rw,exec,size=1g',
                           '--tmpfs', '/root:rw,size=64m',
                           '-v', f'{self.recipes / "corpus"}:/corpus:ro',
                           '-v', f'{self.recipes / "scripts"}:/scripts:ro',
                           '-v', f'{self.cache}:/cache:ro', '-v', f'{self.output(slot)}:/out',
                           self.image, 'sleep', 'infinity']
                container = subprocess.check_output(command, text=True, timeout=45).strip()
                self.containers.append(container)
                worker = {'slot': slot, 'container_id': container, 'creation_command': command,
                          'initialized_utc': self.now()}
                self.record['workers'].append(worker)
                self.save()
                lock = self.exec(slot, ['dpkg-query', '-W', '-f=${binary:Package}\t${Version}\n'], capture=True)
                expected = (self.recipes / self.toolchain / 'lock.txt').read_bytes()
                (self.directory / f'packages-{slot}.txt').write_bytes(lock)
                if lock != expected:
                    raise ValueError(f'worker {slot}: whole installed package lock differs')
                self.verify_tools(slot)
                worker['package_lock_sha256'] = hashlib.sha256(lock).hexdigest()
                self.save()
            return self
        except BaseException as error:
            self.__exit__(type(error), error, error.__traceback__)
            raise

    def verify_tools(self, slot):
        if self.toolchain == 'corpus/toolchain':
            return
        # Recompute the whole non-dpkg Go tree and every tool executable hash;
        # merely comparing dpkg would miss an altered manually installed Go.
        self.exec(slot, ['bash', '-eu', '-c',
            'mkdir -p /tmp/toolchain-verification; python3 -I /' + self.toolchain + '/inventory.py /tmp/toolchain-verification'])
        verified = {}
        for name in ['tools.json', 'go-tree.sha256']:
            actual = self.exec(slot, ['cat', '/tmp/toolchain-verification/' + name], capture=True)
            if actual != (self.recipes / self.toolchain / name).read_bytes():
                raise ValueError(f'worker {slot}: extended tool inventory differs: {name}')
            verified[name] = hashlib.sha256(actual).hexdigest()
        self.record['workers'][slot]['extended_tool_inventory_sha256'] = verified
        self.save()

    def exec(self, slot, command, env=None, capture=False, log=None):
        # env -i also removes Docker image ENV, proxy/credential/cache/compiler overrides.
        clean = {**ENV, **(env or {})}
        if set(clean) - set(ENV) - {'CORPUS_OPT_LEVEL', 'CORPUS_OPENSSL_CONFIG', 'CORPUS_COLLECT',
                                  'CORPUS_SQLITE_VERSION', 'CORPUS_SQLITE_CONFIG', 'CORPUS_BORINGSSL_CONFIG'}:
            raise ValueError('unexpected environment override')
        command = ['docker', 'exec', self.containers[slot], 'env', '-i',
                   *(f'{k}={v}' for k, v in clean.items()), *command]
        if capture:
            return subprocess.check_output(command, timeout=60)
        if log is None:
            subprocess.run(command, check=True, timeout=60)
        else:
            with log.open('wb') as output:
                subprocess.run(command, stdout=output, stderr=subprocess.STDOUT, check=True)

    def prepare(self, identity, recipe_hashes, repository):
        # Recheck every frozen recipe before each profile. Each build recipe verifies
        # its archive hash inside BOTH workers; cache mounts are read-only.
        for name, expected in recipe_hashes.items():
            if sha(self.recipes / name) != expected:
                raise ValueError(f'frozen recipe changed: {name}')
        if self.recovered:
            profile = self.record['profiles'][-1]
            if profile['identity'] != identity:
                raise ValueError('recovered profile identity differs; refuse workspace reset')
            return {**self.record, 'profiles': [dict(profile)]}
        for slot in range(2):
            self.exec(slot, RESET)
            for path in self.output(slot).iterdir():
                if path.is_dir() and not path.is_symlink():
                    shutil.rmtree(path)
                else:
                    path.unlink()
            (self.output(slot) / 'repository.json').write_text(json.dumps(repository))
        self.profiles += 1
        profile = {'identity': identity, 'sequence': self.profiles, 'started_utc': self.now(),
                   'container_reused': self.profiles > 1,
                   'workspace_reset_verified': True, 'status': 'running'}
        self.record['profiles'].append(profile)
        self.save()
        return {**self.record, 'profiles': [dict(profile)]}

    def complete(self):
        self.record['profiles'][-1].update(status='passed', finished_utc=self.now())
        self.save()
        self.recovered = False

    def __exit__(self, kind, error, traceback):
        if error is not None:
            self.record['failure'] = {'type': type(error).__name__, 'message': str(error), 'utc': self.now()}
        results = []
        for container in self.containers:
            result = subprocess.run(['docker', 'rm', '--force', container], capture_output=True, text=True, timeout=45)
            results.append({'container_id': container, 'exit_code': result.returncode,
                            'stderr': result.stderr})
        self.record.update(stopped_utc=self.now(), removal=results)
        self.save()
