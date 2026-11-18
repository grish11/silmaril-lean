"""Use upstream CMake targets, with explicit optimization and cross toolchains."""
import argparse
import json
from pathlib import Path
import shlex
import subprocess


def command(prefix, flags, configuration):
    if configuration not in {'no-asm', 'asm', 'fips-shared'}:
        raise ValueError('unsupported BoringSSL configuration')
    args = ['cmake', '-S', '.', '-B', 'build', '-G', 'Ninja',
            '-DCMAKE_BUILD_TYPE=Release', '-DCMAKE_EXPORT_COMPILE_COMMANDS=ON',
            '-DBUILD_SHARED_LIBS=ON', '-DBUILD_TESTING=OFF',
            '-DOPENSSL_NO_ASM=' + ('ON' if configuration == 'no-asm' else 'OFF'),
            '-DFIPS=' + ('ON' if configuration == 'fips-shared' else 'OFF')]
    for language, compiler in [('C', 'gcc'), ('CXX', 'g++'), ('ASM', 'gcc')]:
        args += [f'-DCMAKE_{language}_COMPILER={prefix}{compiler}',
                 f'-DCMAKE_{language}_FLAGS={flags}',
                 f'-DCMAKE_{language}_FLAGS_RELEASE=-g0 -DNDEBUG']
    if prefix:
        args += ['-DCMAKE_SYSTEM_NAME=Linux', '-DCMAKE_SYSTEM_PROCESSOR=aarch64',
                 '-DCMAKE_AR=' + prefix + 'ar', '-DCMAKE_RANLIB=' + prefix + 'ranlib',
                 '-DCMAKE_LINKER=' + prefix + 'ld']
    return args


def inputs(root):
    """Executed compiler inputs/headers and public generator/build provenance."""
    build = root / 'build'
    for entry in json.loads((build / 'compile_commands.json').read_text()):
        # compile_commands covers configured but unbuilt targets too. Only
        # preserve a translation unit as executed when its object exists.
        arguments = shlex.split(entry.get('command', ''))
        output = entry.get('output')
        if output is None and '-o' in arguments:
            output = arguments[arguments.index('-o') + 1]
        if output is not None and (Path(entry['directory']) / output).is_file():
            yield Path(entry['directory']) / entry['file']
    for line in (build / 'ninja-deps.txt').read_text().splitlines():
        if line.startswith('    '):
            yield (build / line.strip()).resolve()
    for name in ['CMakeLists.txt', 'cmake', 'include', 'crypto/fipsmodule', 'util', 'gen', 'third_party/fiat']:
        path = root / name
        for p in ([path] if path.is_file() else path.rglob('*')):
            if p.is_file() and (p.suffix in {'.h', '.inc', '.S', '.s', '.pl', '.go', '.cmake', '.lds', '.json', '.md'} or p.name == 'CMakeLists.txt'):
                yield p
    for name in ['LICENSE', 'INCORPORATING.md', 'BUILDING.md', 'go.mod', 'go.sum',
                 'configure-command.json', 'configure.log', 'build.log',
                 'build/compile_commands.json', 'build/build.ninja', 'build/CMakeCache.txt',
                 'build/ninja-commands.txt', 'build/ninja-deps.txt']:
        yield root / name


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--inputs', action='store_true')
    parser.add_argument('arguments', nargs='*')
    args = parser.parse_args()
    if args.inputs:
        for path in sorted(set(inputs(Path.cwd()))):
            print(path)
    else:
        cmd = command(*args.arguments)
        Path('configure-command.json').write_text(json.dumps({'command': cmd,
            'module': 'upstream FIPS_SHARED bcm.o' if args.arguments[2] == 'fips-shared' else 'upstream fipsmodule object-library boundary',
            'validation': 'research configuration; no FIPS validation or certification',
            'assembly': 'upstream committed pregenerated inputs; no local perlasm regeneration; upstream ASM flags may include -Wa,-g'}, indent=2) + '\n')
        print(shlex.join(cmd), flush=True)
        subprocess.run(cmd, check=True)
