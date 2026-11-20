# Container examples

**Experimental API.** The `Containers` region (`Silmaril/Containers/…`) may change; the design is
in [Containers](containers.md).

Seven worked examples: two real static ELFs in OCI images (a no-op and `http-serve`, a
self-contained HTTP server), and five small model programs. Each is a
registered problem of the group `containers.examples`, so its verdict comes from the registry.

| Example | Kind | Runs as | Verified | Verdict |
| --- | --- | --- | --- | --- |
| No-op | real | OCI image → static x86-64 ELF → LPS | no undefined behaviour, exit 0, no events | holds |
| `http-serve` | real | OCI image → static x86-64 ELF → LPS, 8080/tcp published; listens itself | no undefined behaviour; every exit is the exact `HTTP/1.1 200` response then the drained request, or a defined failure | holds |
| Crash | model | killed by `SIGSEGV` | no undefined behaviour, partial correctness | holds |
| Crash | model | killed by `SIGSEGV` | no undefined behaviour, exits | fails: it never exits |
| Thread creation | model | `clone` with `pthread_create`'s flags | no undefined behaviour | fails: undefined under the sequential policy |
| HTTP/1.1 server (model) | model | TCP on 8080, one fixed response | TCP only, only `HTTP/1.1 200 OK`, only declared ports | holds |
| vsock compute | model | vsock port 5005, answers reversed | vsock only, exits 0 after answering | holds |

## Try it

```
lake build Silmaril.Containers.Noop.Thms Silmaril.Containers.Fixtures.Thms \
  Silmaril.Containers.Mini.Thms Silmaril.Containers.Http.Thms Silmaril.Containers.HttpServe.Thms
lake env lean --run examples/containers/Examples.lean              # every example
lake env lean --run examples/containers/Examples.lean http-serve   # one: noop, http-serve, crash, thread, http, vsock
examples/containers/http-serve/docker-test.sh                      # the real server under Docker; curl gets 200
```

`Examples.lean` prints each example: its image (with digests), runtime, machine, clone policy,
profile, specification, the run the theorem proves and the theorems. It runs the model examples on
a sample input and reads the real images from their committed layouts, with the reader the proof
uses. For example:

```
http-serve: a real HTTP/1.1 server on 8080/tcp  [real]  (containers.http_serve.oci_wlp)
  runtime:   Ports.ociRuntime: OCI reader with checked SHA-256, the declared 8080/tcp published, then LPS
  proved run: socket; bind 8080; listen; accept; send the 40-octet response, retrying short sends; read once; exit 0
  image read now: read /http-serve: 1624 bytes, sha256 1515fe73…2f02; loads as a static x86-64 ELF; declares 8080/tcp
  source:    examples/containers/http-serve/http_serve.s
  theorems:  Silmaril.Containers.HttpServe.servesImage, …
```

<details><summary>What <code>http-serve</code>'s theorem says, exactly</summary>

`HttpServe.servesImage` (`wlp`): under `Ports.ociRuntime` — the declared port published (a bind
to it has LPS's port-0 outcomes), the sequential clone policy, every flag oracle, every admissible
launch and connection queue — no run has undefined behaviour, and every run that exits either sent
exactly the 40-octet response and then drained the request (exit 0) or exits 10, 11, 13 or 14
having sent at most a prefix. Partial correctness: a run may wait for a peer or data without end.
See [Containers](containers.md), "A self-contained HTTP server".

</details>

## In the explorer

The **Containers** tab (`#/containers`, built by `make pages`) lists the examples with the
registry's verdicts; each example's page shows its image, shape, digests, runtime, machine,
policy, profile, specification, the proved run, the run computed now, the theorems with their
sources, and the registry's shape, arguments and answers.

## What the verdicts rest on

| | |
| --- | --- |
| Real | The bytes (SHA-256 checked in the kernel), read by the restricted OCI reader (`Containers.Oci`), loaded by LPS's x86-64 loader, run by the LPS model of Linux (`Containers.Lps`) for every resolution of x86's undefined flags and every launch LPS admits. `docker-test.sh` runs the same image under Docker as a test. |
| Model | A small program of a model machine (`Mini`, the fixtures' `Tiny`) standing for the container's program. The HTTP response is parsed by the verified HTTP/1.1 parser (`Http.okResponse_parses`); the HTTP interface is valid and admissible under `tcpOnly` (`Http.httpIface_valid`, `httpIface_admissible`). |
| Every example | No undefined behaviour is part of every verified specification; thread creation is undefined under the sequential clone policy; the machine is a parameter of the runtime (`Mach.MachRuntime`). |
