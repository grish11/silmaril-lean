#!/usr/bin/env bash
# Differential test of the HTTP responder image under Docker. A test, not a proof.
#
# What it checks:
#  1. (when GNU as and ld are present) `http_ok.s`, built by the LPS probe build, is the pinned ELF
#     (SHA-256 ac076e37...51d1) and the file in the image's layer;
#  2. Docker loads ./layout with image ID sha256:<config digest> proved in
#     Silmaril.Containers.HttpOnce.Thms, one layer, and the declared port 8080/tcp;
#  3. one container run (no network, read-only root, no capabilities, no new privileges) exits 0
#     and writes exactly the 40 octets `HTTP/1.1 200 OK\r\nContent-Length: 2\r\n\r\nok` to stdout,
#     nothing to stderr: the full-write run of `Thms.full_run`;
#  4. over TCP: a host-side accept loop on 127.0.0.1:$HTTP_ONCE_PORT (default 8080) connects each
#     accepted connection to the standard output of a fresh container (inetd style), and `curl`
#     receives status 200 with body `ok`.
#
# Trust boundary: the theorems are about the LPS model of Linux (x86-64, every flag oracle, every
# admissible launch), the restricted OCI reader and the sequential clone policy. The accept loop
# in step 4 is this script's, not the image's, and no theorem describes it, Docker, runc or the
# host kernel. A pass is evidence about this host; a failure is a counterexample to the model's
# fidelity here (or a harness bug).
#
# Usage: examples/containers/http-once/docker-test.sh   (skips, exit 0, when docker is absent)
# DOCKER_RUN_FLAGS replaces `--network none` (the container needs no network: it writes stdout).
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../.." && pwd)
elf=ac076e372af6ece5fce3a67e3d91c2099ae5f22d390c84145f2380fb3c5a51d1
config=bec586dacb76754d9fd173bf89ff2ff17b8e43af5a8ce4f6c8b552cb5f7f5a1a
layer=a97c6a7d6320f73a7c3d34f17546070a24be9a33f9d62d64f40358ace9ec4280
port=${HTTP_ONCE_PORT:-8080}
tag=silmaril-http-once:pinned

tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
printf 'HTTP/1.1 200 OK\r\nContent-Length: 2\r\n\r\nok' > "$tmp/expected"

(cd "$here/layout" && sha256sum --quiet -c <(for f in blobs/sha256/*; do echo "${f##*/}  $f"; done))
python3 -I - "$here/layout/blobs/sha256/$layer" "$tmp/from-layer" <<'PY'
import sys, tarfile
with tarfile.open(sys.argv[1]) as t:
    names = t.getnames()
    assert names == ["http-ok"], names
    open(sys.argv[2], "wb").write(t.extractfile("http-ok").read())
PY
echo "$elf  $tmp/from-layer" | sha256sum --quiet -c
echo "1. the layer holds the pinned ELF ($elf)"
if command -v as > /dev/null && command -v ld > /dev/null; then
  sh "$root/examples/verification-projects/theorem-dev/lps-probes/build.sh" "$here/http_ok.s" "$tmp/built"
  if echo "$elf  $tmp/built" | sha256sum --quiet -c; then
    echo "   http_ok.s rebuilds to it"
  else
    echo "   note: http_ok.s rebuilt with this binutils differs (the pinned bytes are what is proved)"
  fi
fi

if ! command -v docker > /dev/null || ! docker info > /dev/null 2>&1; then
  echo "skip: docker is not available"
  exit 0
fi

tar -C "$here/layout" -cf "$tmp/image.tar" oci-layout index.json manifest.json blobs
docker load -i "$tmp/image.tar" > /dev/null
id=$(docker image inspect --format '{{.Id}}' "$tag")
[ "$id" = "sha256:$config" ] || { echo "FAIL: image id $id, expected sha256:$config"; exit 1; }
layers=$(docker image inspect --format '{{json .RootFS.Layers}}' "$tag")
[ "$layers" = "[\"sha256:$layer\"]" ] || { echo "FAIL: layers $layers"; exit 1; }
ports=$(docker image inspect --format '{{json .Config.ExposedPorts}}' "$tag")
[ "$ports" = '{"8080/tcp":{}}' ] || { echo "FAIL: exposed ports $ports"; exit 1; }
echo "2. docker loaded $tag as sha256:$config, exposing 8080/tcp"

run=(docker run --rm ${DOCKER_RUN_FLAGS:---network none} --read-only --cap-drop ALL
  --security-opt no-new-privileges)
set +e
"${run[@]}" "$tag" > "$tmp/stdout" 2> "$tmp/stderr"
code=$?
set -e
[ "$code" = 0 ] && cmp -s "$tmp/stdout" "$tmp/expected" && [ ! -s "$tmp/stderr" ] ||
  { echo "FAIL: exit $code, stdout $(wc -c < "$tmp/stdout") octets, stderr $(wc -c < "$tmp/stderr")"; exit 1; }
echo "3. one run: exit 0, stdout is the 40-octet response, stderr empty"

python3 -I - "$port" "$tmp/ready" "${run[@]}" -i "$tag" > "$tmp/server.log" 2>&1 <<'PY' &
import socket, subprocess, sys
port, ready, cmd = int(sys.argv[1]), sys.argv[2], sys.argv[3:]
with socket.create_server(("127.0.0.1", port)) as srv:
    open(ready, "w").close()
    conn, _ = srv.accept()
    with conn:
        code = subprocess.run(cmd, stdin=subprocess.DEVNULL, stdout=conn.fileno()).returncode
        conn.shutdown(socket.SHUT_WR)
        print("container exit status", code)
        sys.exit(code)
PY
server=$!
for _ in $(seq 50); do [ -e "$tmp/ready" ] && break; sleep 0.1; done
curl -sS --http1.1 --max-time 60 -o "$tmp/body" -w '%{http_code}' "http://127.0.0.1:$port/" > "$tmp/status"
wait "$server" || { echo "FAIL: accept loop"; cat "$tmp/server.log"; exit 1; }
[ "$(cat "$tmp/status")" = 200 ] && [ "$(cat "$tmp/body")" = ok ] ||
  { echo "FAIL: curl status $(cat "$tmp/status"), body $(cat "$tmp/body")"; exit 1; }
echo "4. curl http://127.0.0.1:$port/ through the accept loop: status 200, body ok"
echo "PASS (a test of this host, not a proof)"
