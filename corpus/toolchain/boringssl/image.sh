#!/usr/bin/env bash
# Build a separately identified extension, then copy its inventory WITHOUT
# starting a verification container. Artifact pools verify this lock again.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
tag=silmaril-corpus-toolchain-boringssl:trixie-20251103-go1.27.4
base=$(docker image inspect --format '{{.Id}}' silmaril-corpus-toolchain:trixie-20251103)
output=${1:?usage: image.sh OUTPUT_DIRECTORY}
mkdir -p "$output"
# Legacy builder enforces these per-RUN resource limits. Its cpuset shares the
# two host-controller CPUs, within 8 CPUs / 32 GiB alongside the 2-worker pool.
DOCKER_BUILDKIT=0 docker build --network host --cpuset-cpus 0,1 --memory 6g \
  --build-arg "CORPUS_BASE=$base" -t "$tag" "$here" >&2
image=$(docker image inspect --format '{{.Id}}' "$tag")
copy_container=$(docker create --network host --cpus 1 --memory 256m "$image" true)
trap 'docker rm "$copy_container" >/dev/null' EXIT
docker cp "$copy_container:/toolchain/." "$output/"
python3 -I - "$here/../lock.txt" "$output/lock.txt" <<'PY'
from pathlib import Path
import sys
def packages(path):
    return dict(line.split('\t') for line in Path(path).read_text().splitlines())
base, actual = map(packages, sys.argv[1:])
changed = {p: (v, actual.get(p)) for p, v in base.items() if actual.get(p) != v}
if changed:
    raise SystemExit(f'extension changed standard base packages: {changed}')
PY
printf '%s\n' "$image" > "$output/image-id.txt"
printf '%s\n' "$base" > "$output/base-image-id.txt"
printf '%s\n' "$image"
