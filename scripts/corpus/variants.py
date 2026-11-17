#!/usr/bin/env python3
"""Build real optimization/stripping variants, serially, in the pinned corpus image.

Both clean builds must match; both stripping variants must pass existing package
tests before publication. Existing output paths are never overwritten.
"""
import argparse
import atexit
import gzip
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import tomllib
import uuid

ROOT = Path(__file__).resolve().parents[2]
PACKAGES = ['cjson', 'darkhttpd', 'tcp-pingpong', 'mimalloc', 'jemalloc', 'refcrypto', 'tinycc', 'coreutils', 'sqlite', 'openssl']
TAG = 'silmaril-corpus-toolchain:trixie-20251103'
BASE = 'debian:trixie-20251103@sha256:01a723bf5bfb21b9dda0c9a33e0538106e4d02cce8f557e118dd61259553d598'
POSTPROCESSORS = []


def cleanup():
    for container in POSTPROCESSORS:
        subprocess.run(['docker', 'stop', container], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)


atexit.register(cleanup)


def sha(path):
    with path.open('rb') as f:
        return hashlib.file_digest(f, 'sha256').hexdigest()


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--package', choices=PACKAGES, action='append')
    p.add_argument('--arch', choices=['x86_64', 'aarch64'], action='append')
    p.add_argument('--level', choices=['O0', 'Og', 'O1', 'O3'], action='append')
    p.add_argument('--configuration', choices=['asm', 'no-asm'], help='OpenSSL only; default remains no-asm')
    p.add_argument('--work', type=Path, required=True)
    p.add_argument('--resume', action='store_true', help='validate and retain already published builds')
    a = p.parse_args()
    if a.configuration is not None and a.package != ['openssl']:
        p.error('--configuration requires exactly --package openssl')
    os.chdir(ROOT)
    cache = Path(os.environ.get('CORPUS_CACHE', str(Path.home() / '.cache/silmaril-corpus'))).resolve()
    cache.mkdir(parents=True, exist_ok=True)
    a.work = a.work.resolve()
    a.work.mkdir(parents=True, exist_ok=True)
    image = subprocess.check_output(['docker', 'image', 'inspect', '--format', '{{.Id}}', TAG], text=True).strip()
    revision = subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip()
    dirty = bool(subprocess.check_output(['git', 'status', '--porcelain'], text=True).strip())
    # Freeze recipes so an editor or another branch cannot change a long build midway.
    recipes = a.work / ('recipes-' + str(uuid.uuid4()))
    shutil.copytree(ROOT / 'corpus', recipes / 'corpus', ignore=shutil.ignore_patterns('upstream', 'generated', 'elf', 'funcmap', 'tv', 'census', 'variants', 'measurements', '__pycache__'))
    shutil.copytree(ROOT / 'scripts/corpus', recipes / 'scripts/corpus', ignore=shutil.ignore_patterns('__pycache__'))
    recipe_hashes = {str(f.relative_to(recipes)): sha(f) for f in recipes.rglob('*') if f.is_file()}

    for pkg in a.package or PACKAGES:
        subprocess.run(['bash', str(recipes / 'corpus' / pkg / 'fetch.sh')], env={**os.environ, 'CORPUS_CACHE': str(cache)}, check=True)
        package = tomllib.loads((recipes / 'corpus' / pkg / 'package.toml').read_text())
        for arch in a.arch or ['x86_64', 'aarch64']:
            canonical = json.loads((ROOT / 'corpus/elf' / pkg / arch / 'receipt.json').read_text())
            names = [obj['object'] for obj in canonical['outputs']]
            for level in a.level or ['O0', 'Og', 'O1', 'O3']:
                config = (a.configuration or 'no-asm') if pkg == 'openssl' else 'default'
                relative = Path('corpus/variants') / pkg / package['version'] / config / arch / level
                dest = ROOT / relative
                if dest.exists():
                    if not a.resume:
                        raise FileExistsError(f'{dest}: preserve existing outputs; use --resume to validate and retain')
                    existing = json.loads((dest / 'build.json').read_text())
                    if (existing['project'], existing['version'], existing['optimization'], existing['target'], existing['configuration']) != (pkg, package['version'], level, arch + '-linux-gnu', config):
                        raise ValueError(f'{dest}: identity mismatch')
                    for variant in ['unstripped', 'stripped']:
                        receipt = json.loads((dest / variant / 'receipt.json').read_text())
                        if not receipt['reproducible']:
                            raise ValueError(f'{dest}: reproducibility not established')
                        for obj in receipt['outputs']:
                            if sha(ROOT / obj['path']) != obj['sha256']:
                                raise ValueError(f'{dest}: artifact changed')
                    for source in existing['included_source_files']:
                        if sha(ROOT / source['path']) != source['sha256']:
                            raise ValueError(f'{dest}: included source changed')
                    print(f'retained {relative}: existing hashes validated; no new run claimed', flush=True)
                    continue
                run_id = str(uuid.uuid4())
                work = a.work / run_id
                work.mkdir()
                processor = None

                def docker(command, log, extra=()):
                    nonlocal processor
                    base_cmd = ['docker', 'run', '--rm', '--network', 'host', '--cpus', '8', '--memory', '32g',
                           '-e', 'JOBS=8', '-e', 'SOURCE_DATE_EPOCH=1762128000', '-e', f'CORPUS_OPT_LEVEL={level}', '-e', f'CORPUS_OPENSSL_CONFIG={config}',
                           '-v', f'{recipes / "corpus"}:/corpus:ro', '-v', f'{recipes / "scripts"}:/scripts:ro',
                           '-v', f'{cache}:/cache:ro', '-v', f'{work}:/out', *extra]
                    # Measure tools inside the container, not just the Docker client.
                    measured = ['python3', '-I', '/scripts/corpus/measure.py',
                        '--stage', log.stem, '--target', arch + '-linux-gnu', '--output', '/out/runs',
                        '--repository-receipt', '/out/repository.json', '--concurrency', '8' if log.stem.startswith('build-') else '1',
                        '--input', f'/corpus/{pkg}/build.sh', '--input', '/corpus/common.sh', '--', *command]
                    if log.stem.startswith('build-'):
                        wrapped = [*base_cmd, image, *measured]
                    else:
                        if processor is None:
                            processor = subprocess.check_output([*base_cmd, '-d', image, 'sleep', 'infinity'], text=True).strip()
                            POSTPROCESSORS.append(processor)
                        wrapped = ['docker', 'exec', processor, *measured]
                    with log.open('wb') as output:
                        subprocess.run(wrapped, stdout=output, stderr=subprocess.STDOUT, check=True)

                (work / 'repository.json').write_text(json.dumps({'commit': revision, 'dirty': dirty, 'recipe_hashes': recipe_hashes}))
                for repeat in ['a', 'b']:
                    (work / repeat).mkdir()
                    extra = ['-e', 'CORPUS_COLLECT=/out/collected'] if repeat == 'a' else []
                    docker(['bash', f'/corpus/{pkg}/build.sh', arch, '/out/' + repeat], work / f'build-{repeat}.log', extra)
                for name in names:
                    if sha(work / 'a' / name) != sha(work / 'b' / name):
                        raise ValueError(f'{pkg}/{arch}/{level}/{name}: clean builds differ')
                (work / 'unstripped').mkdir()
                (work / 'stripped').mkdir()
                (work / 'stripped-b').mkdir()
                for variant in ['unstripped', 'stripped']:
                    for name in names + ['.build-info']:
                        shutil.copy(work / 'a' / name, work / variant / name)
                prefix = '' if arch == 'x86_64' else 'aarch64-linux-gnu-'
                for name in names:
                    docker([prefix + 'strip', '--strip-all', '/out/stripped/' + name], work / ('strip-' + name + '.log'))
                    shutil.copy(work / 'b' / name, work / 'stripped-b' / name)
                    docker([prefix + 'strip', '--strip-all', '/out/stripped-b/' + name], work / ('strip-b-' + name + '.log'))
                    if sha(work / 'stripped' / name) != sha(work / 'stripped-b' / name):
                        raise ValueError(f'{name}: stripped clean builds differ')
                    docker(['python3', '-I', '/scripts/corpus/variant_pair.py', arch,
                            '/out/unstripped/' + name, '/out/stripped/' + name, '/out/' + name + '.pair.json'],
                           work / ('pair-' + name + '.log'))
                for variant in ['unstripped', 'stripped']:
                    docker(['bash', f'/corpus/{pkg}/test.sh', arch, '/out/' + variant], work / f'test-{variant}.log')
                    docker(['python3', '-I', '/corpus/receipt.py', '/corpus/' + pkg, arch, '/out/' + variant,
                            'true', TAG, image, BASE], work / f'receipt-{variant}.log')
                    receipt_path = work / variant / 'receipt.json'
                    receipt = json.loads(receipt_path.read_text())
                    for obj in receipt['outputs']:
                        obj['path'] = str(relative / variant / obj['object'])
                    receipt['variant'] = {'optimization': level, 'stripping': variant, 'configuration': config,
                                          'run_id': run_id, 'target': arch + '-linux-gnu'}
                    if variant == 'stripped':
                        receipt['reproducibility_check'] = 'two byte-identical clean builds, independently stripped with the pinned tool in a separate post-processing container, byte-identical stripped outputs'
                    receipt_path.write_text(json.dumps(receipt, indent=2) + '\n')
                stage = Path(tempfile.mkdtemp(prefix='variant-publish-', dir=a.work))
                for variant in ['unstripped', 'stripped']:
                    shutil.copytree(work / variant, stage / variant, ignore=shutil.ignore_patterns('.*'))
                collected = work / 'collected'
                sources = []
                for source in sorted((collected / 'upstream').rglob('*')):
                    if not source.is_file():
                        continue
                    rel = source.relative_to(collected / 'upstream')
                    canonical_source = ROOT / 'corpus' / pkg / 'upstream' / rel
                    if not canonical_source.exists() or sha(source) != sha(canonical_source):
                        # Preserve extra exact archive inputs in this build, never edit existing upstream bytes.
                        target = stage / 'upstream' / rel
                        target.parent.mkdir(parents=True, exist_ok=True)
                        shutil.copy(source, target)
                        source_path = relative / 'upstream' / rel
                    else:
                        source_path = canonical_source.relative_to(ROOT)
                    sources.append({'path': str(source_path), 'sha256': sha(source)})
                if (collected / 'generated').exists():
                    shutil.copytree(collected / 'generated', stage / 'generated')
                    for source in sorted((stage / 'generated').rglob('*')):
                        if source.is_file():
                            sources.append({'path': str(relative / source.relative_to(stage)), 'sha256': sha(source)})
                for f in work.glob('*.pair.json'):
                    shutil.copy(f, stage / f.name)
                shutil.copytree(work / 'runs', stage / 'runs')
                logs = stage / 'logs'
                logs.mkdir()
                for log in work.glob('*.log'):
                    (logs / (log.name + '.gz')).write_bytes(gzip.compress(log.read_bytes(), mtime=0))
                (stage / 'build.json').write_text(json.dumps({'schema_version': 1, 'run_id': run_id,
                    'project': pkg, 'version': package['version'], 'configuration': config,
                    'target': arch + '-linux-gnu', 'optimization': level, 'image_id': image,
                    'source_inputs': canonical['inputs'], 'included_source_files': sources,
                    'license': package['license'], 'license_files': package.get('license_files', []),
                    'recipe_revision': revision, 'recipe_worktree_dirty': dirty, 'recipe_hashes': recipe_hashes,
                    'environment': {'JOBS': 8, 'SOURCE_DATE_EPOCH': 1762128000, 'LC_ALL': 'C', 'TZ': 'UTC'},
                    'reproducibility': 'two clean containers, byte-identical outputs',
                    'lean_status': 'not generated or checked', 'source_semantics_status': 'not bound',
                    'binary_equivalence_status': 'no functional equivalence statement instantiated'}, indent=2) + '\n')
                dest.parent.mkdir(parents=True, exist_ok=True)
                if dest.exists():
                    raise FileExistsError(dest)
                shutil.move(str(stage), dest)
                if processor is not None:
                    subprocess.run(['docker', 'stop', processor], stdout=subprocess.DEVNULL, check=True)
                    POSTPROCESSORS.remove(processor)
                print(f'published {relative}: {len(names) * 2} real ELF artifacts; clean reproducibility, tests, paired stripping passed', flush=True)


if __name__ == '__main__':
    main()
