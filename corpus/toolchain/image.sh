#!/usr/bin/env bash
# Build the corpus toolchain image with a fixed tag and print its image id.
# Docker here has no bridge network, hence --network host.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
TAG=silmaril-corpus-toolchain:trixie-20251103
docker build --network host -t "$TAG" "$here" >&2
docker image inspect --format '{{.Id}}' "$TAG"
