"""Select a hash-pinned SQLite source release for both acquisition and build."""
import os
from pathlib import Path
import tomllib

version = os.environ.get('CORPUS_SQLITE_VERSION', '3.54.1')
releases = tomllib.loads(Path(__file__).with_name('releases.toml').read_text())
if version not in releases:
    raise SystemExit(f'unsupported SQLite source version: {version}')
release = releases[version]
for value in [version, release['root'], release['sha256'], release['url']]:
    print(value)
