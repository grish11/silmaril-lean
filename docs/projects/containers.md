# Containers: a pluggable framework for verifying container images

This page describes the `Containers` region (`Silmaril/Containers/…`, see
[regions.toml](../../regions.toml)): what a container image is at several levels of detail, what a
containerised process does to its environment, what a runtime adds, and which predicates on an
image's contents make a specification hold. The goal is a framework in which Docker images, and
later Kubernetes workloads, are verified against interface specifications **relative to an explicit
runtime model**, with every trust, loader, resource and security assumption stated.

## Summary and status

Statuses follow [HTTP servers](http-servers.md): **Proved** (a theorem in a `Thms` header, standard
axioms only), **Checked** (evaluated on examples by `#guard`), **Defined** (definitions without
theorems), **Planned** (nothing exists yet). No module uses `sorry`, `native_decide` or new axioms.

| Layer | Module | Status |
| --- | --- | --- |
| Content-addressed stores: integrity (`Sound`) and binding (`InjOn`) kept apart; checking; decoding | `Containers.Cas` | Proved |
| Images: flat trees, layered manifests over stores, flattening, shapes, configurations and ports | `Containers.Image` | Proved (flattening, shapes); OCI octets Planned |
| Environment: events, capabilities, profiles (`none`, `stdio`, `vsockOnly`, `tcpOnly`, `udpOnly`, `networkOnly`, `networkUnix`, `readOnlyFs`), confinement, declared ports | `Containers.Env` | Proved |
| Behaviours: stops (exit, own signal, runtime kill, refusal), blocking, silent divergence, infinite runs; safety, partial and total correctness, assumptions, fairness, determinism up to inputs, noninterference | `Containers.Behaviour` | Proved |
| Runtime models: loader, process semantics, runtime-added behaviours; assumption strengthening, kills, enforcement | `Containers.Runtime` | Proved |
| Machine semantics (pluggable): states, labelled steps, final states; runs with undefined behaviour explicit (stuck, no initial state, task creation); task-creation requests classified by `CLONE_THREAD`/`CLONE_VM`; the sequential policy; the transfer obligation to other machines | `Containers.Machine` | Proved |
| Preconditions: semantic `pre`; the verification precondition `vpre` (no undefined behaviour and the specification); `wlp`, `wp`; sufficiency, feasibility, assertion languages, representability, concrete sufficient preconditions | `Containers.Precondition` | Proved |
| A minimal machine: exact runs, exact `wlp`/`wp` on contents, thread creation, `vfork`, `fork`, falling off the end, spinning | `Containers.Mini` | Proved; Checked (`Examples`) |
| Fixtures under the small runtime model: no-op, crash, spin, HTTP over TCP, vsock compute | `Containers.Fixtures` | Proved; Checked (`Examples`) |
| HTTP interfaces (version, transport, port), admissibility under profiles, the server platform of a runtime model, the fixture's response parsed by the verified HTTP/1.1 parser | `Containers.Http` | Proved |
| The behaviour institution and its logic-graph registration | `Containers.Institution`, `LogicGraph.Nodes.Containers` | Proved (satisfaction condition) |
| A sequential x86-64 machine instance; a parallel x86-64 machine; ELF images under the Linux process semantics; OCI octets; Nitro Enclaves; Redis; Kubernetes | — | Planned (below) |

**What the fixtures do and do not show.** Every fixture theorem is relative to `Fixtures.small`: a
tiny program language whose semantics is written down directly. Nothing here runs Docker, runc or a
kernel, and the executable checks in `Fixtures.Examples` evaluate the model, not a runtime. The
fixtures exist to pin down the shape of statements (which spec, under which runtime model, with
which assumption) before the process semantics is replaced by a real one.

## What the repository already had, and how this connects

| Existing development | Used for |
| --- | --- |
| `Servers.Platform` (`Platform`, `SockEv`, `Platform.linux`, `Platform.container` over a layered `Image`) | `Containers.Http.platform` reads any runtime model's runs as a server platform; `platform_view_iff_linux` shows it is the Linux process platform at the socket semantics it defines, so `Platform.Sat`, `Platform.Refines` and `Platform.connModel` (the core server institution) apply |
| `Servers.Core` (server institution as `Sig ⥤ Room`), `Cli.Institution` | the template for `Containers.Inst` |
| `Net.Http1` (HTTP/1.1 heads, a verified parser with round-trip theorems) | `Http.okResponse_parses`: the fixture's octets parse to `HTTP/1.1 200` |
| `Net.Ip.Addr` (`Port`, `SockAddr`) | ports and addresses in events and configurations |
| `Crypto.Interface.HashFn` (functional interface; security deliberately not a field) | `Cas.Store.Verified`; collision resistance stays a hypothesis |
| `Logic.Institution` (`Room`, `Inst`), `Project.Registry.Institution` | the behaviour institution and its registration |
| `Elf` (facts over one file, `ExeLoaded`, `CliExe`), `Process` (LPS, `RunOutcome`) | Planned instances of `Shape` and `ProcSem` (below) |
| `Formats` (JSON, tar, gzip/DEFLATE with proofs), `Crypto.SHA256` | Planned OCI octet level |
| `Machine.Behaviour.Outcome` (`returned`, `trapped`, `faulted`, `undefined`, `exhausted`, `diverges`) | Planned: the outcome relation of compiled code maps into `Stop` and `Beh` |

`Servers.Platform.container` already models a container as a process started from a layered image.
`Containers` refines that picture: images are read from content stores by digest, the program is
found by a shape, and the runtime is a parameter with its own behaviours.

## Architecture

```
          Cas.Store D C  ──decode──▶  Image (Layered D ──flatten──▶ Flat C)
                                              │ Shape C P (finds the program)
                                              ▼
 Runtime I P E = load : I → Except Refusal P  ×  sem : ProcSem P E  ×  obs : Beh E → Beh E → Prop
                                              │ beh
                                              ▼
                 Model E (sets of runs) ── Sat ── Spec E (safety / partial / total / under A)
                                              │ pre R φ : I → Prop  (on contents when I = Flat C)
                                              ▼
                 Assertions I ── Representable / SufficientIn (concrete preconditions)
```

**Pluggability.** Each arrow is a parameter:

* *Contents* `C` are abstract (programs in the fixtures; octets read through the ELF API later).
* *Shapes* (`Shape C P`, with `ShapeKind` = `static`, `dynamic`, `script`, `wasm`, `distro`) say how
  a runtime finds the program.
* *Process semantics* (`ProcSem P E := P → Model E`) is any set-of-runs semantics. It is usually
  built from a *machine semantics* (`Mach.MachineSem P E`, `Runtime.ofMachine`): the machine's
  state carries its memory model, threads and scheduler, so the machine, memory and concurrency
  model are parameters of the runtime model, not a fixed sequential executable semantics.
* *What the runtime adds* (`obs`) is separate from the program: `Runtime.exact`, `mayKill`,
  `enforce`, `restrict`.
* *Specifications* are predicates on runs. An abstract HTTP specification is a sentence of the
  server institution, reached through `Http.platform`; a Wasm implementation is compared by
  behavioural refinement on the same platform (`Platform.Refines`), as the `Servers` region already
  does for `wasi:http` components against a Linux server loop.

## Correctness distinctions the definitions keep apart

| Distinction | Where | Result |
| --- | --- | --- |
| Safety vs partial vs total correctness | `Spec.safe`, `Spec.partialCorrect`, `Spec.totalCorrect` | `Model.sat_partialCorrect_of_noExit`: a model that never exits satisfies every partial-correctness spec; `Fixtures.crash_wlp`, `crash_not_wp` |
| Behaviour refinement vs trace inclusion | `Model.Refines`, `Model.TraceRefines` | `traceRefines_not_total`; `Fixtures.spin_traceRefines_noop`, `spin_not_refines_noop` |
| Silent divergence vs blocking on the environment | `Beh.spins`, `Beh.blocked` | total correctness *under* an environment assumption (`Spec.under Beh.notBlocked`): `Fixtures.nitro_total` |
| Fairness | `Beh.InfinitelyOften`, `Spec.under` | Defined; liveness of servers under fairness is in `Servers.Live` |
| Strengthening runtime assumptions vs admitting runtime behaviours | `Runtime.restrict`, `Runtime.mayKill` | `restrict_le`, `le_mayKill`; `safe_mayKill`, `partialCorrect_mayKill`, `totalCorrect_not_mayKill` |
| A program's own crash vs a runtime kill vs a refusal | `Stop.signaled`, `Stop.killed`, `Stop.refused` | `pre_refused`: a refused image satisfies every `wlp` |
| Environmental vs internal nondeterminism | `Ev.isInput`, `Model.DetUpToInputs` | `Fixtures.echoOnce_det`, `coin_not_det` |
| Noninterference is relational | `Model.Noninterference` | `noninterference_not_trace_property`; `trace_property_not_noninterference`: memory safety, no-ACE or profile confinement (all trace properties) do not imply it |
| Profile proved of a program vs enforced by a runtime | `Confined`, `Runtime.enforce` | `enforce_confined` (for runs without undefined behaviour), `enforce_eq_of_confined`; `Fixtures.http_enforce_vsock` |
| Runtime-added behaviours never hide undefined behaviour | `Runtime.ObsKeepsUB`, `Runtime.PreservesUB`; `restrict` and `enforce` keep every run with undefined behaviour | `preservesUB_restrict`, `preservesUB_mayKill`, `preservesUB_enforce`; `noUB_restrict_iff`, `noUB_mayKill_iff`, `noUB_enforce_iff`; `not_vpre_of_preservesUB`; `Mini.threadSpawn_not_wlp_restrict`, `_mayKill`, `_enforce`, `_restrict_noUB` |
| A digest names content; it does not prove it | `Store.Sound`, `Store.InjOn`, `Store.checked` | `sound_checked`, `agree_of_sound` (needs binding), `digest_not_binding`; `Fixtures.Examples`: a tampered store runs the wrong program unless checked |
| Undefined behaviour is an outcome, not an absence of runs | `Stop.undefined`, `UB`, `Mach.MachineSem.Run` (stuck, `noInit`, `clone` give runs) | `not_wlp_of_stuck`, `not_wlp_of_clone`, `not_wlp_of_noInit`; `Mini.fallOff_not_wlp` |
| Every verification precondition excludes undefined behaviour | `vpre R φ := pre R (noUB ∧ φ)`; `wlp`, `wp` | `not_vpre_of_undefined`; `Mini.wlp_iff` (exact: `noUB ∧ partialCorrect`); `Mini.threadSpawn_partial` shows partial correctness alone holds of a thread-creating program |
| No undefined behaviour vs termination and progress | `Spec.noUB`, `Spec.terminates` | `Spec.noUB_spins`, `Spec.terminates_undefined`; `Mini.spinForever_wlp`, `spinForever_not_wp` |
| Refinement up to undefined behaviour is vacuous against undefined abstractions | `Model.ubClose`, `Model.RefinesUB` | `refinesUB_vacuous`, `refinesUB_of_noUB` |
| Sequential results do not transfer to a parallel machine by themselves | `Mach.SeqAgrees` | `wlp_transfer` needs it as a hypothesis |
| Semantic weakest preconditions vs expressible ones | `pre`, `Representable`, `Expressive`, `SufficientIn` | `pre_weakest` (semantic, always exists); expressiveness is a hypothesis (`sufficientIn_of_expressive`); `Fixtures.wp_exit0_iff` computes one exactly, `noopCheck_sufficient` is a decidable sufficient one |
| Feasibility (no miracles) | `Feasible` | `pre_of_infeasible` |

## Machines, undefined behaviour and concurrency

**The machine is a named parameter of the runtime.** `Mach.MachRuntime I P E` has three
fields: `load` (images to programs), `machine : MachineSem P E`, and `obs` (what the runtime
adds, `Eq` by default); `toRuntime` is its runtime model and `withMachine M` swaps the machine and
nothing else. The construction is exact (`MachRuntime.beh_iff`): the runs of an image are the
loader's refusal, or `obs` applied to the machine's runs of the loaded program. `Mach.MachineSem P E` has states, the initial states of a
program (a relation: layout randomisation and initial memory are nondeterministic), steps labelled
by actions (`ev e` with the environment, `tau`, `clone r` for task creation) and final states.
`Runtime.ofMachine load M` is a runtime model over it. The runs (`MachineSem.Run`) are read from
finite executions, as described in the module: final states give stops, a state with no step and
no final outcome gives `undefined stuck`, a program with no initial state gives
`undefined noInit`, and a task-creation request gives `undefined (r.ub)`. **Undefined behaviour
always produces a run**, so it cannot make a precondition hold vacuously. Infinite runs with
infinitely many events are the limit closure of finite executions; this can only add runs, which
makes preconditions stronger, never weaker.

**Undefined behaviour under runtime-added behaviours.** "No undefined behaviour" is a property of
the runs the environment sees, which are program (machine) runs transformed by what the runtime
adds. The runtime may add runs, for example a kill truncating a program run (that run ends in
`killed`, which is not undefined behaviour), but it must not remove a program run that has
undefined behaviour. This is required, not assumed: `Runtime.ObsKeepsUB` for what a runtime adds,
`Runtime.PreservesUB` between models, and all three transformers satisfy it:

* `restrict A` (strengthening an assumption) keeps the runs satisfying `A` **and every run with
  undefined behaviour**: an assumption about the environment or the runtime never excuses the
  program, so even `restrict Spec.noUB` certifies nothing new (`Mini.threadSpawn_not_wlp_restrict_noUB`);
* `mayKill` adds truncated runs and keeps the original ones;
* `enforce` stops a run at its first event outside the profile, **except a run with undefined
  behaviour, which is kept as it is**: in reality a faithful enforcer may stop the process before
  the undefined behaviour, but certifying an image must not depend on that, and a run with undefined
  behaviour may do things the filter does not observe. So `enforce_confined` is stated for runs
  without undefined behaviour.

Hence `noUB_restrict_iff`, `noUB_mayKill_iff`, `noUB_enforce_iff`: no undefined behaviour holds
after each transformer exactly when it holds before. A runtime-defined `obs` outside these
transformers must be shown to keep undefined behaviour (`ObsKeepsUB`) before
`MachRuntime.not_vpre_of_run` applies. Undefined behaviour of the container runtime itself (a
runtime bug) is outside these models and is an assumption about the runtime.

**"No undefined behaviour" is part of every verification precondition.** `vpre R φ` requires
that *every* run of the image under `R` (every admissible execution: every environment input,
every internal choice, every runtime-added behaviour, under the runtime model's assumptions)
has no undefined behaviour, and satisfies `φ`. `wlp` and `wp` are `vpre` of partial and total
correctness. No undefined behaviour is a safety property of a run. It is neither termination nor
progress: a spinning program satisfies `wlp` and not `wp`.

**The first machine: threads are undefined behaviour.** The sequential policy reads a
task-creation request by its flags (`CloneReq.kind`):

| Request (x86-64 system call) | Flags | Kind | Sequential policy |
| --- | --- | --- | --- |
| `clone` (56) or `clone3` (435) with `CLONE_THREAD` (`0x10000`), e.g. glibc `pthread_create` (`0x3d0f00`) | contains `CLONE_THREAD` | thread | `UB.threadCreate` |
| `vfork` (58); `clone`/`clone3` with `CLONE_VM` (`0x100`) and not `CLONE_THREAD`, e.g. glibc `posix_spawn` | contains `CLONE_VM` | shared address space | `UB.threadCreate` |
| `fork` (57); `clone`/`clone3` with neither | neither | process | `UB.unmodeled` |

The trigger is the request, not its success: `clone(CLONE_THREAD)` without `CLONE_SIGHAND` and
`CLONE_VM`, which Linux rejects with `EINVAL`, is still classified a thread; this only rejects
more programs. Processes are `unmodeled`, not undefined in the C sense, but the effect on
verification is the same: no claim is made, and `wlp` fails. That an instance maps these four
system calls, and nothing else, to `clone` actions is the instance's obligation
(`MachineSem.ClonesExplicit`). The only instance so far, `Mini.mini`, has `clone` as an
instruction and decodes no system calls; **no system call coverage is claimed**.

**Towards a parallel x86-64 machine.** It will be another `MachineSem` with explicit threads in
its state, a scheduler whose choices are quantified over (fairness as a stated assumption where
liveness needs it), shared memory under x86-TSO (store buffers, `MFENCE`, `LOCK`-prefixed atomic
read-modify-write), and whatever the machine declares undefined (`UB.memory`), with refinement
obligations between it and the sequential machine. Transfer of a sequential result is not
automatic: `wlp_transfer` needs `SeqAgrees` (every run of the image under the parallel runtime
is a run under the sequential one), a theorem to be proved, for example for programs that never
make a task-creation request, from a proof that the parallel machine restricted to one thread
refines the sequential one.

## Nitro Enclaves

`Profile.vsockOnly` describes only the channels of the process *inside* an enclave. An AWS Nitro
Enclave is not "a Docker container restricted to vsock":

* **Build.** `nitro-cli build-enclave` converts a Docker image into an enclave image file (EIF): a
  kernel, its command line and an initramfs holding the image's root file system and an init. The
  container runtime is not present at run time.
* **Measurement.** The EIF's sections are hashed into platform configuration registers (PCR0: the
  whole image; PCR1: kernel and boot ramdisk; PCR2: the application). Optional PCR8 binds a signing
  certificate.
* **Boot and runtime.** The Nitro hypervisor starts a separate VM with dedicated vCPUs and memory, no
  persistent storage, no external network and a single vsock device; the parent instance (CID 3) is
  outside the trust boundary and is the only peer.
* **Attestation.** The enclave obtains an attestation document (COSE_Sign1, certificate chain to the
  AWS Nitro root) over the PCRs and caller-supplied data from the Nitro Secure Module.

Plan (`Containers.Nitro`, not yet written): a runtime model whose images are EIFs (a new level
below `Flat`), whose loader is the EIF boot path (obligations: the PCR values computed from the EIF
equal the expected ones; the initramfs root file system is the flattened OCI image), whose process
semantics is that of the init and the application, and whose enforcement is `vsockOnly` *by
construction of the VM*, stated as an assumption about the hypervisor, not proved. Attestation
verification is a separate protocol obligation (signature validity under `Crypto.Interface.Signature`
with an EUF-CMA assumption as data). `Fixtures.nitro` is only the application-level part.

Source: AWS, *AWS Nitro Enclaves User Guide*, sections "Nitro Enclaves concepts" and
"Cryptographic attestation", <https://docs.aws.amazon.com/enclaves/latest/user/>.

## Real images: loading Redis

Target: the official `redis` image for `linux/amd64`, pinned by the digest of its platform manifest.
The obligations, in the order a proof meets them:

1. **Trust (octets).** A pinned manifest digest; every blob read through `Store.checked` with
   SHA-256 (`Crypto.SHA256`), so integrity is checked, not assumed; binding (`Store.InjOn`) is the
   named collision-resistance assumption of SHA-256, recorded as data. Provenance (who built the
   image, Sigstore signatures, SLSA attestations) is a separate, optional obligation and implies
   nothing about behaviour.
2. **Format (octets → layered).** OCI image index, manifest and configuration as JSON
   (`Formats` JSON); layers as gzip-compressed tar (`Formats` gzip and tar, with proofs), with OCI
   whiteouts (`.wh.<name>`) and opaque directories (`.wh..wh..opq`), which `Tree.apply` does not yet
   model. The decoder is proved left-inverse to an encoder, so `Cas.sound_decode` carries integrity
   up.
3. **Shape.** The official image is Debian-based: its entry point `docker-entrypoint.sh` is a shell
   script (shape `script`) that may re-execute itself as user `redis` through `gosu` before running
   `/usr/local/bin/redis-server`, a dynamically linked PIE (shape `dynamic`). A first proof should fix
   the entry point to `redis-server` (an explicit configuration override) rather than model the
   script.
4. **Loader.** ELF facts over the octets at that path, through the ELF API: `KindIs … pie`,
   `Exe.InterpIs … /lib64/ld-linux-x86-64.so.2`, `Needed` (libc, libm and, if built with TLS, libssl
   and libcrypto), every undefined symbol resolved by `Lookup` in the load scope, `NoTextRelD`; then
   `ExeLoaded`. That relation transcribes glibc 2.39's `ld.so`; Debian's glibc version must match it
   or the transcription must be extended, an explicit trust gap.
5. **Machine and process semantics.** A `MachineSem` instance from LPS (`Process.LPS`) for the
   syscalls Redis uses at startup and on its request path (`socket`, `bind`, `listen`, `epoll_*`, `accept` or `accept4`, `read`, `write`, `fsync`,
   `clock_gettime`, `getrandom`, …). LPS's `error unmodeled` becomes `UB.unmodeled`, a stuck LPS
   state `UB.stuck`, and `clone`/`clone3`/`fork`/`vfork` become `clone` actions, so they are excluded
   by every `wlp`, never silent successes. Redis starts background threads (`bio` threads for lazy
   freeing and file closing, I/O threads when configured), so **under the sequential machine its
   `wlp` fails**: verifying it needs the parallel machine, or a configuration and build proved
   never to create threads (Redis starts its `bio` threads unconditionally at startup in the
   versions we know of; this must be checked against the pinned version).
6. **Resources.** A memory limit (cgroup) and `maxmemory`; the file-descriptor limit (`maxclients`
   needs about 32 more descriptors than clients); CPU. Out-of-memory kills are `Runtime.mayKill`, so
   safety and partial correctness survive and total correctness does not.
7. **Security.** The profile is `networkOnly` on 6379/tcp plus file writes under `/data` for
   persistence (and `unixSockets` if `unixsocket` is configured); runtime enforcement is Docker's
   default seccomp profile, dropped capabilities and a non-root user, modelled by `Runtime.enforce`
   whose faithfulness to seccomp is an assumption. None of this gives noninterference between
   clients.
8. **Specification.** RESP over TCP as an interface of the server institution, with the key-value
   commands linearizable against a sequential map (`Servers.State` already has key-value state models
   and Herlihy–Wing linearizability). Persistence, replication and modules are out of scope at first.

What can honestly be proved first: items 1–4 and 7 as facts about the pinned octets, and item 8 as a
specification; that `redis-server` implements item 8 is a much larger proof about its C code and is
not claimed.

## Kubernetes (later)

A pod is a set of containers sharing a network namespace and volumes, so its environment is shared
(the profile of the pod is the union, and `localhost` traffic between containers is internal). The
parts that change the semantics, beyond composing runtime models:

* **Restart policies** turn a crash into a new run: the observed behaviour of a restarted container
  is a sequence of runs, so total correctness of one run becomes a property of restarts under a
  fairness assumption on the kubelet.
* **Probes** (liveness, readiness) are liveness specifications checked by the environment, and a
  failing liveness probe is a runtime kill (`Kill.external`).
* **Resource limits** are `mayKill (· = .oom)`; **NetworkPolicy** restricts the addresses of events,
  a finer profile than capabilities.
* **Rolling updates** are refinement between two versions' runtime models.

## Tables

The data in this development is meant to be recorded as rows, as the logic graph and the
consequence-system registry already are:

| Table | Row | Source |
| --- | --- | --- |
| `institutions`, `rooms` | `containers.behaviour` | registered (`LogicGraph.Nodes.Containers`) |
| `container_profiles` | profile name, capabilities | `Env.Profile` (planned record kind) |
| `container_shapes` | shape kind, program type | `Image.ShapeKind` (planned) |
| `container_runtimes` | runtime model, its assumptions and added behaviours | `Runtime` instances (planned) |
| `container_obligations` | image, runtime, specification, kind (trust, loader, resource, security, behaviour), status (proved, checked, assumed, open) | planned problem shapes `silmaril.shapes.containers.*`, in the style of `Elf.CliExe` |

A container check can be a consequence system: `Γ ⊢ φ` with `Γ` the image's contents and `φ` a
specification, interpreted by `pre R φ` (planned `consequence_interpretation containers.pre`).

## Requested and not yet done

These are part of the original request and remain open after this pull request:

* **Real images and real execution.** No OCI image is parsed and no ELF file is loaded or run under
  `Process.LPS` in this development; nothing is executed in a container runtime, and no fixture has
  been compared with Docker. The fixtures are models (`Fixtures.small`, `Mini.machR`).
* **A sequential x86-64 machine instance** with `ClonesExplicit` proved for system calls 56, 57, 58
  and 435, and LPS's `unmodeled`, fault and stuck outcomes mapped to `UB`.
* **The parallel x86-64 machine** (threads, scheduler, x86-TSO, atomics) and `SeqAgrees` proofs.
* **Acceptors, consequence systems and tables.** Only the institution and its room are registered
  (`LogicGraph.Nodes.Containers`). Not done: a `consequence_interpretation` reading
  `vpre R φ` as `Γ ⊢ φ` over image contents; an `Acceptor` for decidable content checkers such as
  `Fixtures.noopCheck` with `CorrectInterleaved`; record kinds and problem shapes
  (`silmaril.shapes.containers.*`) for profiles, shapes, runtime models and obligations; and the
  database tables of the "Tables" section. These need a decision on placement: the registry lives
  in the `Project` region, whose `deps` do not include `Containers`.
* **Nitro Enclaves** (EIF, PCRs, attestation), **Redis**, **Kubernetes**: designed above, not
  implemented.

## Next steps

1. OCI octets: JSON manifests, tar layers with whiteouts, SHA-256 checked stores, the decoder and
   its round trip.
2. A sequential x86-64 `MachineSem` with thread creation as undefined behaviour, and its
   `ClonesExplicit` proof; a `static` shape over ELF octets and a `ProcSem` from LPS (`RunOutcome` and socket events to
   `Beh Ev`), first on a static ELF that exits 0, then on the hello server of `Servers.LinuxHello`.
3. The parallel x86-64 machine (threads, scheduler, x86-TSO, atomics) and `SeqAgrees` for
   programs without task creation.
4. Hiding events (partial observation maps) with divergence made explicit, as a construction on
   the institution.
5. The Nitro runtime model with EIF measurement obligations.
6. Problem shapes and record kinds for profiles, shapes, runtime models and obligations.

## References

* Goguen and Burstall, *Institutions: abstract model theory for specification and programming*,
  J. ACM 39(1), 1992 (`goguen-burstall-1992` in `references.bib`).
* Alpern and Schneider, *Defining liveness*, Inf. Process. Lett. 21(4), 1985,
  doi:10.1016/0020-0190(85)90056-0 (safety and liveness).
* Clarkson and Schneider, *Hyperproperties*, J. Comput. Secur. 18(6), 2010,
  doi:10.3233/JCS-2009-0393 (noninterference is not a trace property).
* Zdancewic and Myers, *Observational determinism for concurrent program security*, CSFW 2003,
  doi:10.1109/CSFW.2003.1212703 (the form of `Model.Noninterference`).
* Dijkstra, *Guarded commands, nondeterminacy and formal derivation of programs*, CACM 18(8), 1975,
  doi:10.1145/360933.360975 (weakest and weakest liberal preconditions).
* Sewell, Sarkar, Owens, Zappa Nardelli and Myreen, *x86-TSO: a rigorous and usable
  programmer's model for x86 multiprocessors*, CACM 53(7), 2010, doi:10.1145/1785414.1785443
  (the planned memory model of the parallel machine).
* Linux `clone(2)` and `clone3` (`include/uapi/linux/sched.h` for the flag values;
  `arch/x86/entry/syscalls/syscall_64.tbl` for the numbers 56, 57, 58, 435).
* Open Container Initiative, *Image Format Specification* v1.1.0,
  <https://github.com/opencontainers/image-spec/tree/v1.1.0> (manifests, layers, whiteouts).
* RFC 9112 §2.3 (`HTTP-version`), RFC 9114 §3 (HTTP/3 over QUIC).

No artifact of these sources is bundled or quoted beyond the definitions named, so no artifact
hashes are recorded here.

## Checking it

```
lake build --wfail Silmaril.Containers.Fixtures.Examples Silmaril.Containers.Mini.Examples \
  Silmaril.Containers.Http.Thms \
  Silmaril.Containers.Institution.Defs Silmaril.LogicGraph.Nodes.Containers.Defs
```
