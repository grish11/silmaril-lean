#!/usr/bin/env bash
set -euo pipefail

if [[ $# != 3 || ( $1 != --check && $1 != --write ) ]]; then
  echo "Usage: $0 {--check|--write} QUINT_CHECKOUT APALACHE_TGZ" >&2
  exit 2
fi

mode=$1
quint=$(cd "$2" && pwd)
fixtures=$(cd "$(dirname "$0")" && pwd)
quint_sha=95141d4691cce7e60104bdfcbc1d1b074f1cb789
apalache_version=0.62.4
apalache_sha=8ac8488422c30d552735bae11b92a2d014d8e02e8608702acc08f9a2d8a9abb2

if [[ $(git -C "$quint" rev-parse HEAD) != "$quint_sha" ]] ||
   ! git -C "$quint" diff --quiet "$quint_sha" -- quint; then
  echo "Use a clean Quint checkout at $quint_sha" >&2
  exit 1
fi
cli="$quint/quint/dist/src/cli.js"
if [[ ! -f $cli ]]; then
  echo "Run npm ci in $quint/quint to build the pinned CLI" >&2
  exit 1
fi
archive_hash=$(sha256sum < "$3")
if [[ ${archive_hash%% *} != "$apalache_sha" ]]; then
  echo "Apalache archive SHA-256 mismatch, expected $apalache_sha" >&2
  exit 1
fi

work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
export QUINT_HOME="$work/quint-home"
dist="$QUINT_HOME/apalache-dist-$apalache_version"
mkdir -p "$dist"
tar -xzf "$3" -C "$dist"
cd "$work"

modules=(BoundedCounter BitPair)
for module in "${modules[@]}"; do
  cp "$fixtures/$module.qnt" .
  # A fresh loopback port avoids Quint's default reuse of an already running server.
  port=$(node -e "const server = require('node:net').createServer()
    server.listen(0, '127.0.0.1', () => {
      console.log(server.address().port)
      server.close()
    })")
  node "$cli" compile "$module.qnt" --target=tlaplus --main="$module" --init=init --step=step \
    --apalache-version="$apalache_version" --server-endpoint="127.0.0.1:$port" --verbosity=0 > "$module.tla"

  printf 'INIT q_init\nNEXT q_step\n' > "$module.cfg"
  if ! java -Xmx512m -XX:+UseParallelGC -cp "$dist/apalache/lib/apalache.jar" tlc2.TLC \
      -deadlock -workers 1 -dump dot "$module.dot" "$module.tla" > "$module.tlc.log" 2>&1; then
    cat "$module.tlc.log" >&2
    exit 1
  fi
done
node "$fixtures/check.cjs" "$quint" "$work"

for module in "${modules[@]}"; do
  if [[ $mode == --check ]]; then
    cmp "$fixtures/$module.tla" "$module.tla"
  else
    cp "$module.tla" "$fixtures/"
  fi
done
cd "$fixtures"
if [[ $mode == --check ]]; then
  sha256sum -c SHA256SUMS
else
  sha256sum BitPair.qnt BitPair.tla BoundedCounter.qnt BoundedCounter.tla oracle.json > SHA256SUMS
fi
