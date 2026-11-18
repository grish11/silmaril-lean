#!/usr/bin/env python3
"""Build real optimization/stripping variants, serially, in the pinned corpus image.

Both clean builds must match; both stripping variants must pass existing package
tests before publication. Existing output paths are never overwritten.
"""
import argparse
import gzip
import hashlib
import json
import os
import signal
from pathlib import Path
from container_pool import ContainerPool
import shutil
import subprocess
import tempfile
import tomllib
import uuid

ROOT = Path(__file__).resolve().parents[2]
PACKAGES = ['cjson', 'darkhttpd', 'tcp-pingpong', 'mimalloc', 'jemalloc', 'refcrypto', 'tinycc', 'coreutils', 'sqlite', 'openssl', 'boringssl']
TAG = 'silmaril-corpus-toolchain:trixie-20251103'
BASE = 'debian:trixie-20251103@sha256:01a723bf5bfb21b9dda0c9a33e0538106e4d02cce8f557e118dd61259553d598'

def parse_profile(value):
    parts = value.split(':')
    if (len(parts) != 3 or parts[1] not in ['x86_64', 'aarch64'] or
            parts[2] not in ['O0', 'Og', 'O1', 'O2', 'O3']):
        raise argparse.ArgumentTypeError('profile must be CONFIGURATION:ARCH:LEVEL')
    return tuple(parts)


def profile_axes(package, profiles):
    allowed = {'openssl': {'asm', 'no-asm'}, 'boringssl': {'asm', 'no-asm', 'fips-shared'},
               'sqlite': {'default', 'fts5-rtree', 'small'}}.get(package, {'default'})
    if any(config not in allowed for config, arch, level in profiles):
        raise ValueError('profile configuration is unsupported for this package')
    return tuple(list(dict.fromkeys(profile[i] for profile in profiles)) for i in [1, 0, 2])


def sha(path):
    with path.open('rb') as f:
        return hashlib.file_digest(f, 'sha256').hexdigest()


def main():
    def interrupted(signum, frame):
        raise KeyboardInterrupt(f'signal {signum}')
    signal.signal(signal.SIGTERM, interrupted)
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--package', choices=PACKAGES, action='append')
    p.add_argument('--arch', choices=['x86_64', 'aarch64'], action='append')
    p.add_argument('--level', choices=['O0', 'Og', 'O1', 'O2', 'O3'], action='append',
                   help='explicit O2 builds add separately repeated strip pairs; default remains O0/Og/O1/O3')
    p.add_argument('--configuration', choices=['asm', 'no-asm', 'default', 'fts5-rtree', 'small', 'fips-shared'], action='append', help='package-specific build configuration; OpenSSL/BoringSSL default remains no-asm')
    p.add_argument('--version', action='append', help='SQLite only: a pinned genuine upstream release')
    p.add_argument('--profile', type=parse_profile, action='append',
                   help='exact CONFIGURATION:ARCH:LEVEL tuple; repeat to share one pool without a Cartesian matrix')
    p.add_argument('--work', type=Path, required=True)
    p.add_argument('--resume-pool', type=Path, help='reconnect to the same idle workers; never create replacements')
    p.add_argument('--recover-work', type=Path, help='unpublished profile with two successfully measured builds')
    p.add_argument('--resume', action='store_true', help='validate and retain already published builds')
    a = p.parse_args()
    if a.profile:
        if len(a.package or []) != 1 or a.arch or a.configuration or a.level:
            p.error('--profile requires one --package and cannot combine with --arch/--configuration/--level')
        try:
            a.arch, a.configuration, a.level = profile_axes(a.package[0], a.profile)
        except ValueError as error:
            p.error(str(error))
    if a.configuration is not None and not a.profile:
        allowed = {'openssl': {'asm', 'no-asm'}, 'boringssl': {'asm', 'no-asm', 'fips-shared'},
                   'sqlite': {'default', 'fts5-rtree', 'small'}}
        if not a.package or len(a.package) != 1 or not set(a.configuration) <= allowed.get(a.package[0], set()):
            p.error('--configuration requires exactly --package openssl (asm/no-asm), boringssl (asm/no-asm/fips-shared), or sqlite (default/fts5-rtree/small)')
    if a.version:
        releases = tomllib.loads((ROOT / 'corpus/sqlite/releases.toml').read_text())
        if a.package != ['sqlite'] or not set(a.version) <= releases.keys():
            p.error('--version requires exactly --package sqlite and a pinned release')
    if bool(a.resume_pool) != bool(a.recover_work) or (a.resume_pool and not a.resume):
        p.error('--resume-pool and --recover-work require each other and --resume')
    if 'boringssl' in (a.package or []) and a.package != ['boringssl']:
        p.error('BoringSSL requires a separate invocation with its extended pinned toolchain')
    tag = 'silmaril-corpus-toolchain-boringssl:trixie-20251103-go1.27.4' if a.package == ['boringssl'] else TAG
    toolchain = 'corpus/toolchain/boringssl' if a.package == ['boringssl'] else 'corpus/toolchain'
    os.chdir(ROOT)
    cache = Path(os.environ.get('CORPUS_CACHE', str(Path.home() / '.cache/silmaril-corpus'))).resolve()
    cache.mkdir(parents=True, exist_ok=True)
    a.work = a.work.resolve()
    a.work.mkdir(parents=True, exist_ok=True)
    image = subprocess.check_output(['docker', 'image', 'inspect', '--format', '{{.Id}}', tag], text=True).strip()
    revision = subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip()
    dirty = bool(subprocess.check_output(['git', 'status', '--porcelain'], text=True).strip())
    if a.resume_pool:
        a.resume_pool = a.resume_pool.resolve()
        a.recover_work = a.recover_work.resolve()
        if not a.recover_work.is_relative_to(a.work) or not a.resume_pool.is_relative_to(a.work):
            p.error('recovery paths must be inside --work')
        pool_record = json.loads((a.resume_pool / 'lifecycle.json').read_text())
        creation = pool_record['workers'][0]['creation_command']
        recipes = Path(next(item for item in creation if item.endswith(':/corpus:ro')).removesuffix(':/corpus:ro')).parent
        repository = json.loads((a.recover_work / 'repository.json').read_text())
        if repository != json.loads((a.resume_pool / '0/repository.json').read_text()):
            raise ValueError('recovery repository/recipe identity mismatch')
        revision, dirty, recipe_hashes = repository['commit'], repository['dirty'], repository['recipe_hashes']
        controller = {'revision': subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip(),
                      'hashes': {name: sha(ROOT / name) for name in
                                 ['scripts/corpus/variants.py', 'scripts/corpus/container_pool.py']}}
        pool_context = ContainerPool.reconnect(a.resume_pool, recipes, cache, image, controller, toolchain=toolchain)
    else:
        # Freeze recipes so an editor or another branch cannot change a long build midway.
        recipes = a.work / ('recipes-' + str(uuid.uuid4()))
        shutil.copytree(ROOT / 'corpus', recipes / 'corpus', ignore=shutil.ignore_patterns('upstream', 'generated', 'elf', 'funcmap', 'tv', 'census', 'variants', 'measurements', '__pycache__'))
        shutil.copytree(ROOT / 'scripts/corpus', recipes / 'scripts/corpus', ignore=shutil.ignore_patterns('__pycache__'))
        recipe_hashes = {str(f.relative_to(recipes)): sha(f) for f in recipes.rglob('*') if f.is_file()}
        pool_context = ContainerPool(image, recipes, cache, a.work / ('pool-' + str(uuid.uuid4())), toolchain=toolchain)

    with pool_context as pool:
        for pkg in a.package or [pkg for pkg in PACKAGES if pkg != 'boringssl']:
            metadata = tomllib.loads((recipes / 'corpus' / pkg / 'package.toml').read_text())
            for version in a.version or [metadata['version']]:
                package = {**metadata, 'version': version}
                fetch_env = {**os.environ, 'CORPUS_CACHE': str(cache)}
                if pkg == 'sqlite':
                    fetch_env['CORPUS_SQLITE_VERSION'] = version
                subprocess.run(['bash', str(recipes / 'corpus' / pkg / 'fetch.sh')], env=fetch_env, check=True)
                for arch in a.arch or ['x86_64', 'aarch64']:
                    names = [obj['name'] for obj in package['object']]
                    for config in (a.configuration or ['no-asm']) if pkg in ['openssl', 'boringssl'] else (a.configuration or ['default']):
                        for level in a.level or ['O0', 'Og', 'O1', 'O3']:
                            if a.profile and (config, arch, level) not in a.profile:
                                continue
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
                            run_id = a.recover_work.name if pool.recovered else str(uuid.uuid4())
                            work = a.recover_work if pool.recovered else a.work / run_id
                            if not pool.recovered:
                                work.mkdir()
                            repository = {'commit': revision, 'dirty': dirty, 'recipe_hashes': recipe_hashes}
                            lifecycle = pool.prepare(str(relative), recipe_hashes, repository)
                            first, second = pool.output(0), pool.output(1)

                            def docker(command, log, slot=0, collect=False):
                                env = {'CORPUS_OPT_LEVEL': level}
                                if pkg == 'openssl':
                                    env['CORPUS_OPENSSL_CONFIG'] = config
                                elif pkg == 'boringssl':
                                    env['CORPUS_BORINGSSL_CONFIG'] = config
                                elif pkg == 'sqlite':
                                    env.update(CORPUS_SQLITE_CONFIG=config, CORPUS_SQLITE_VERSION=version)
                                if collect:
                                    env['CORPUS_COLLECT'] = '/out/collected'
                                measured = ['python3', '-I', '/scripts/corpus/measure.py',
                                    '--stage', log.stem, '--target', arch + '-linux-gnu', '--output', '/out/runs',
                                    '--repository-receipt', '/out/repository.json',
                                    '--concurrency', '3' if log.stem.startswith('build-') else '1',
                                    '--input', f'/corpus/{pkg}/build.sh', '--input', '/corpus/common.sh', '--', *command]
                                if log.exists():
                                    log.rename(log.with_name(log.stem + '.pre-reconnect-' + str(uuid.uuid4()) + '.log'))
                                pool.exec(slot, measured, env=env, log=log)

                            (work / 'repository.json').write_text(json.dumps({'commit': revision, 'dirty': dirty, 'recipe_hashes': recipe_hashes}))
                            if pool.recovered:
                                for slot, repeat in enumerate(['a', 'b']):
                                    runs = [json.loads(f.read_text()) for f in (pool.output(slot) / 'runs').glob('*.json')]
                                    builds = [r for r in runs if r['stage'] == 'build-' + repeat]
                                    if len(builds) != 1 or builds[0]['exit_code'] != 0 or builds[0]['repository'] != repository:
                                        raise ValueError('recovery requires two successful measured builds of the same frozen inputs')
                                    for name in names + ['.build-info']:
                                        if sha(work / repeat / name) != sha(pool.output(slot) / repeat / name):
                                            raise ValueError('completed build changed before recovery')
                            else:
                                for slot, repeat in enumerate(['a', 'b']):
                                    (pool.output(slot) / repeat).mkdir()
                                    docker(['bash', f'/corpus/{pkg}/build.sh', arch, '/out/' + repeat],
                                           work / f'build-{repeat}.log', slot=slot, collect=(slot == 0))
                                    shutil.copytree(pool.output(slot) / repeat, work / repeat)
                            if (work / 'a/.build-info').read_bytes() != (work / 'b/.build-info').read_bytes():
                                raise ValueError(f'{relative}: independently recorded build inputs/commands differ')
                            for name in names:
                                if sha(work / 'a' / name) != sha(work / 'b' / name):
                                    raise ValueError(f'{pkg}/{arch}/{level}/{name}: clean builds differ')
                            supplementary = []
                            extra_a, extra_b = work / 'a/supplementary', work / 'b/supplementary'
                            files_a = {f.relative_to(extra_a): sha(f) for f in extra_a.rglob('*') if f.is_file()}
                            files_b = {f.relative_to(extra_b): sha(f) for f in extra_b.rglob('*') if f.is_file()}
                            if files_a != files_b:
                                raise ValueError(f'{relative}: supplementary clean repeats differ')
                            for name, digest in sorted(files_a.items()):
                                supplementary.append({'path': str(relative / 'supplementary' / name),
                                    'sha256': digest, 'kind': 'ET_REL' if name.suffix == '.o' else 'module provenance',
                                    'stripping': 'not stripped; no strip-all linkability claim',
                                    'reproducibility': 'byte-identical independent workspace repeats'})
                            for variant in ['unstripped', 'stripped']:
                                (first / variant).mkdir(exist_ok=True)
                                for name in names + ['.build-info']:
                                    shutil.copy(work / 'a' / name, first / variant / name)
                            (second / 'stripped-b').mkdir(exist_ok=True)
                            prefix = '' if arch == 'x86_64' else 'aarch64-linux-gnu-'
                            for name in names:
                                docker([prefix + 'strip', '--strip-all', '/out/stripped/' + name], work / ('strip-' + name + '.log'))
                                shutil.copy(work / 'b' / name, second / 'stripped-b' / name)
                                docker([prefix + 'strip', '--strip-all', '/out/stripped-b/' + name], work / ('strip-b-' + name + '.log'), slot=1)
                                if sha(first / 'stripped' / name) != sha(second / 'stripped-b' / name):
                                    raise ValueError(f'{name}: stripped clean builds differ')
                                docker(['python3', '-I', '/scripts/corpus/variant_pair.py', arch,
                                        '/out/unstripped/' + name, '/out/stripped/' + name, '/out/' + name + '.pair.json'],
                                       work / ('pair-' + name + '.log'))
                            for variant in ['unstripped', 'stripped']:
                                docker(['bash', f'/corpus/{pkg}/test.sh', arch, '/out/' + variant], work / f'test-{variant}.log')
                            for variant, folder in [('unstripped', 'b'), ('stripped', 'stripped-b')]:
                                docker(['bash', f'/corpus/{pkg}/test.sh', arch, '/out/' + folder],
                                       work / f'test-{variant}-b.log', slot=1)
                            lifecycle['profiles'][0].update(status='passed', finished_utc=pool.now())
                            for variant in ['unstripped', 'stripped']:
                                docker(['python3', '-I', '/corpus/receipt.py', '/corpus/' + pkg, arch, '/out/' + variant,
                                        'true', tag, image, BASE], work / f'receipt-{variant}.log')
                                receipt_path = first / variant / 'receipt.json'
                                receipt = json.loads(receipt_path.read_text())
                                for obj in receipt['outputs']:
                                    obj['path'] = str(relative / variant / obj['object'])
                                receipt['variant'] = {'optimization': level, 'stripping': variant, 'configuration': config,
                                                      'run_id': run_id, 'target': arch + '-linux-gnu'}
                                receipt['reproducibility_check'] = ('two clean workspaces in independent persistent pool containers; byte-identical outputs'
                                    + ('; independently stripped in their respective workers; byte-identical stripped outputs' if variant == 'stripped' else ''))
                                receipt['container_pool'] = lifecycle
                                repeat_folder = 'b' if variant == 'unstripped' else 'stripped-b'
                                receipt['independent_repeat_tests'] = [json.loads(line) for line in
                                    (second / repeat_folder / '.tests.jsonl').read_text().splitlines() if line.strip()]
                                receipt_path.write_text(json.dumps(receipt, indent=2) + '\n')
                            # Present only this completed profile to the existing census
                            # tool. Container-local symlinks keep original receipt paths
                            # without mounting the host repository into a build worker.
                            view = first / 'census-input'
                            for variant in ['unstripped', 'stripped']:
                                link = view / relative / variant
                                link.parent.mkdir(parents=True, exist_ok=True)
                                link.symlink_to('/out/' + variant, target_is_directory=True)
                            docker(['env', f'CORPUS_ANALYSIS_IMAGE_ID={image}', 'python3', '-I',
                                    '/scripts/corpus/census.py', '--root', '/out/census-input',
                                    '--variants-only', '--output', '/out/census'], work / 'census.log')
                            stage = Path(tempfile.mkdtemp(prefix='variant-publish-', dir=a.work))
                            if supplementary:
                                shutil.copytree(extra_a, stage / 'supplementary')
                            for variant in ['unstripped', 'stripped']:
                                shutil.copytree(first / variant, stage / variant, ignore=shutil.ignore_patterns('.*'))
                            collected = first / 'collected'
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
                            for f in first.glob('*.pair.json'):
                                shutil.copy(f, stage / f.name)
                            shutil.copytree(first / 'runs', stage / 'runs')
                            shutil.copytree(second / 'runs', stage / 'runs', dirs_exist_ok=True)
                            logs = stage / 'logs'
                            logs.mkdir()
                            for log in work.glob('*.log'):
                                (logs / (log.name + '.gz')).write_bytes(gzip.compress(log.read_bytes(), mtime=0))
                            (stage / 'build.json').write_text(json.dumps({'schema_version': 1, 'run_id': run_id,
                                'project': pkg, 'version': package['version'], 'configuration': config,
                                'target': arch + '-linux-gnu', 'optimization': level, 'image_id': image,
                                'source_inputs': receipt['inputs'], 'included_source_files': sources,
                                'supplementary_artifacts': supplementary,
                                'license': package['license'], 'license_files': package.get('license_files', []),
                                'recipe_revision': revision, 'recipe_worktree_dirty': dirty, 'recipe_hashes': recipe_hashes,
                                'environment': {'JOBS': 3, 'SOURCE_DATE_EPOCH': 1762128000, 'LC_ALL': 'C', 'TZ': 'UTC'},
                                'reproducibility': 'two clean workspaces in independent persistent pool containers, byte-identical outputs',
                                'container_pool': lifecycle,
                                'lean_status': 'not generated or checked', 'source_semantics_status': 'not bound',
                                'binary_equivalence_status': 'no functional equivalence statement instantiated'}, indent=2) + '\n')
                            dest.parent.mkdir(parents=True, exist_ok=True)
                            if dest.exists():
                                raise FileExistsError(dest)
                            census_files = []
                            for report in (first / 'census').rglob('*.json'):
                                target = ROOT / 'corpus/census' / report.relative_to(first / 'census')
                                if target.exists():
                                    raise FileExistsError(target)
                                census_files.append((report, target))
                            shutil.move(str(stage), dest)
                            for report, target in census_files:
                                target.parent.mkdir(parents=True, exist_ok=True)
                                shutil.copy(report, target)
                            pool.complete()
                            print(f'published {relative}: {len(names) * 2} real ELF artifacts; clean reproducibility, tests, paired stripping passed', flush=True)


if __name__ == '__main__':
    main()
