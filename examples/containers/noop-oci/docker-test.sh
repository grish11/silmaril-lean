#!/usr/bin/env bash
# Differential test of the no-op image under Docker. A test, not a proof.
#
# What it checks: Docker loads the OCI layout in ./layout, assigns it the image ID
# sha256:<config digest> proved in Silmaril.Containers.Noop.Thms, and a container run with no
# network, a read-only root, no capabilities and no new privileges exits 0 with empty stdout and
# stderr. That is the observable part of `Silmaril.Containers.Noop.beh_image` (one run,
# `done [] (exited 0)`), observed once on this host.
#
# Trust boundary: the theorem is about the LPS model of Linux (x86-64, every flag oracle, every
# admissible launch), the restricted OCI reader and the sequential clone policy. This script
# exercises Docker, runc and the host kernel, none of which the theorem describes; a pass is
# evidence about this host, a failure is a counterexample to the model's fidelity here.
#
# Usage: examples/containers/noop-oci/docker-test.sh   (skips, exit 0, when docker is absent)
# Extra `docker run` flags can be given in DOCKER_RUN_FLAGS (for example `--network host` in
# sandboxes without a bridge network; the default is `--network none`).
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
config=d77f6e9c553c0f0a3c2370fc870c57f500b2a0769f056a757365959928ca0260
layer=c2e4b98bae96ca80b54509d3067c208b6f9d22d9153e6ae80a83c947787a5d14

if ! command -v docker > /dev/null || ! docker info > /dev/null 2>&1; then
  echo "skip: docker is not available"
  exit 0
fi

tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
(cd "$here/layout" && sha256sum --quiet -c <(for f in blobs/sha256/*; do echo "${f##*/}  $f"; done))
tar -C "$here/layout" -cf "$tmp/noop.tar" oci-layout index.json manifest.json blobs
docker load -i "$tmp/noop.tar" > "$tmp/load.txt"
cat "$tmp/load.txt"

id=$(docker image inspect --format '{{.Id}}' silmaril-noop:pinned)
[ "$id" = "sha256:$config" ] || { echo "FAIL: image id $id, expected sha256:$config"; exit 1; }
layers=$(docker image inspect --format '{{json .RootFS.Layers}}' silmaril-noop:pinned)
[ "$layers" = "[\"sha256:$layer\"]" ] || { echo "FAIL: layers $layers"; exit 1; }

set +e
docker run --rm ${DOCKER_RUN_FLAGS:---network none} --read-only --cap-drop ALL \
  --security-opt no-new-privileges silmaril-noop:pinned > "$tmp/stdout" 2> "$tmp/stderr"
code=$?
set -e
echo "exit status: $code, stdout: $(wc -c < "$tmp/stdout") octets, stderr: $(wc -c < "$tmp/stderr") octets"
[ "$code" = 0 ] && [ ! -s "$tmp/stdout" ] && [ ! -s "$tmp/stderr" ] || { echo "FAIL"; exit 1; }
echo "PASS (a test of this host, not a proof)"
