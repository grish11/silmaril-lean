# High-level APIs and Linux process interaction trees

Design proposal for a first slice with regular-file `read`, `write`, `pread`,
`pwrite`, connected-byte-stream `send` and `recv`, and finite pools of threads.
Use weak interaction trees for programs, a relational kernel for admissible
responses, and a scheduler over residual trees for concurrency. A
Goguen–Burstall institution exists for exact, typed, single-exchange lowering
over a fixed execution profile. Use refinement obligations for broader
implementations and compiler lowerings. The constructions and lemmas below
are proposed unless identified as existing.

## Programs, kernels and shared state

Use a signature `Σ = (Req, Resp : Req → Type)`. Its tree event family has
one event of type `Resp(q)` for each request `q`. Index a request by its
operation, capability and arguments. For example, `pread(f,n,p)` requires a
readable regular-file handle and returns an errno or bytes of length at most
`n`. A write takes the bytes and returns an errno or a count bounded by
their length. Give `recv` and `send` the same bounds at a connected-stream
handle. A zero-length success at size zero needs no EOF test. For a positive
request, a zero-byte stream receive denotes end of input in the proposed
profile, and temporary unavailability has a separate outcome. A handle
index records capability and mode. Its resolution to a live descriptor and
the call's buffer and offset guards are semantic obligations.

For fixed `Σ`, the sequential category has value types as objects, arrows
`A → Tree Σ B`, identity `ret` and composition by bind. Equality is pointwise
weak-tree equality. Order the homs pointwise by `TraceLE`. On these weak
trees, mutual inclusion of the full reply-indexed traces implies tree equality.
State can be threaded in the runner, or through an explicit state transformer
when constructing an interpretation. A handler that replaces events with trees
is a separate kind of arrow between event interfaces. Its identity triggers the
same event and composition interprets the first handler's trees with the second.
This extends to a Kleisli functor when the interpretation preserves return and
bind, and transports recursive definitions when it preserves iteration. The
library's complete Elgot fold gives these laws under its universe and smallness
hypotheses. An interpreter returning only the set of terminating results
erases pending prefixes and divergence. [Weak trees and monad laws](../../Silmaril/Semantics/ITree/Thms.lean)
· [Trace antisymmetry](../../Silmaril/Semantics/ITree/Trace/Thms.lean)
· [Ordered Kleisli homs and composition](../../Silmaril/Semantics/ITree/Kleisli/Thms.lean)
· [Handler fold and its hypotheses](../../Silmaril/Semantics/ITreeInterpret/Defs.lean)
· [Initiality](../../Silmaril/Semantics/ITreeInterpret/Thms.lean)

For execution, fix a store `W`, an environment context type `E`, and a
public output alphabet `V`. A kernel relates `(e : E, w : W, q : Req)` to
either `reply(r : Resp(q), w', batch : List V)` or a non-resuming
`stop(reason, finalStore : Option W, batch)`. The stop tags distinguish
process exit, operand or machine fault, client undefined behaviour (UB),
and unsupported model behaviour. A supported Linux errno is a reply
and can resume the tree.
An empty kernel relation at a request gives a pending, blocked configuration
in the fixed environment. An immutable peer script can live in `E` with
its current position in `W`. The first profile evaluates a request in one
atomic completion step. Readiness can be supplied by the environment or a
would-block errno in the API profile. Park/wake and partial syscall
interleavings require an explicit transition extension. A deterministic
example handler is a function choosing one strongly typed outcome or a
declared pending status after reading its state and environment. Its graph
must be included in the relational contract on legal states. Prove enabledness
or a progress condition separately where the contract requires it.

On regular-file success, the relation reads at the cursor for `read`
and at the explicit offset for `pread`. It returns the bytes at that
position up to the permitted transfer count. For `write` and `pwrite`
it replaces the selected file range with the accepted prefix of the
request bytes. Ordinary calls advance the cursor by the count.
Positioned calls leave it fixed. The chosen profile determines the
admitted counts and errno/post-state pairs, including any side effects
on an error path. For streams the relation consumes the accepted RX
prefix or emits the accepted TX prefix and frames the file state.
It preserves byte order across calls. Application message boundaries
are outside the byte-stream profile.

Use one shared store for the file system, descriptor bindings, file cursors
and stream state. Each thread has its own residual continuation. Keep file
identity separate from open-description identity. Independent opens may
share bytes and have different cursors. Threads sharing a handle share its
cursor. Exclude descriptor duplication in the initial LPS bridge unless
aliasing is represented faithfully. Use the sum of the two request families
to dispatch file and stream handlers on this store. A product of separate
stores is a special case with disjoint footprints and frame lemmas. The
two sequential orders of effects need not commute, so a symmetric tensor
of arbitrary shared-state programs would impose an invalid interchange
law. With a shared cursor at zero and file `AB`, two distinct threads
reading one byte return `A` to whichever thread runs first. The pair of
thread-local results depends on that order. Even for disjoint state, a
joint ordered output log can distinguish the orders.

## Scheduled execution and observations

The concurrent configuration consists of a finite pool of tagged residual
trees or returned values, the shared store, and scheduler state. A policy
selects a runnable thread from the current configuration and history or
reports idle. A selected tree returns, exposes its next request, or has
no visible root. Completion updates the shared store and only the selected
continuation. A thread return records its result, and the pool returns the
indexed collection of results when all threads return. Process exit is a
different terminal outcome. A tree with no visible root has a silent
self-loop when selected. A policy with nothing runnable and pending threads
can report blocked. A policy that deliberately idles while work is enabled
can be excluded by a work-conservation guard. If admitted, record policy
idling in the execution history and use it in the progress judgment. Any
repeated idle transitions form a possible infinite execution. Fairness is
a predicate on policy runs. Environment readiness is a separate hypothesis.
The weak tree has erased finite silent steps, so this scheduler works at
observable boundaries and does not count user instructions.
Compose pools by disjoint union of thread IDs and run one policy on the
combined pool. Claims about renaming or rebracketing require transport of
the policy, its histories and any observed IDs along the same bijection.

Embed a sequential tree at a fixed thread ID and choose that thread whenever
it can take a step, including silent divergence. Use identical initial store,
environment moves and kernel. Prove a two-way step correspondence, then lift
it to equal finite observations and corresponding maximal runs after erasing
the fixed thread tag and unwrapping the singleton result. This uses the
singleton policy, or policies shown equivalent to it on the embedding.
Allowing arbitrary idle, or projecting away blocked/unsupported endpoints,
would weaken the claim. The separate machine-level singleton/SC transport
lemmas offer a proof pattern. [Typed scheduler and step](../../Silmaril/Process/TypedSyscall/Defs.lean)
· [Existing machine-level solo correspondence](../../Silmaril/Process/Mt/Thms.lean)

Keep three views of a run available, with explicit projection functions.

- The syscall view records a selected thread's typed request, its typed reply
  when completed, and the batch associated with that completion. A finite
  observation can end at a completed-call boundary or at a pending request.
  A call with an error reply has completed. Retain a separate terminal tag
  for a fault or unsupported call, even if the raw machine history has no
  completed record for it.
- The public view projects batches to the chosen outputs and can flatten them
  to a byte/channel log. It can omit thread IDs, descriptors, return counts
  or file storage, depending on the contract. Close byte observations under
  byte prefixes, including cuts inside a batch. Preserve raw call prefixes
  separately. The projection can send a successful file operation to an
  empty batch.
- The outcome view attaches the chosen terminal result or reason to the
  accumulated output, optionally with a projection of the final store.
  A finite prefix alone makes no termination claim.
  For progress use maximal runs, keeping blocked/stuck, termination, and
  infinite execution distinct. An infinite execution can have a finite
  public log after its last output. Use actual infinite runs for divergence
  claims. For example, a relation that chooses a finite countdown at the first
  step and then terminates has arbitrarily long runs and no infinite run.

`HasTrace` already distinguishes prefix, pending request, completed exchange
and return. `HasVisiblePrefix` counts completed exchanges along some path,
without recovering their labels. For LPS use `StepRecord`, `LStep`, `HStar`,
`byteTrace`, `obsTrace_iff_history` and `RunOutcome` as bridge points.
`PartialWriter.Prefix` and `Runs` in `TraceModels` give an accumulation pattern
for a fixed deterministic handler and policy. Its `ContinuousLog` and
`omegaProduct` apply when the log has the required ordered multiplication
and suprema. For finite syscall words use lists and prefix closure directly.
Plain finite lists with prefix order lack arbitrary joins, and incompatible
logs from different runs must not be combined into a single log.
[ITree traces](../../Silmaril/Semantics/ITree/Trace/Defs.lean)
· [Visible prefix length](../../Silmaril/Semantics/ITree/VisiblePrefix/Defs.lean)
· [LPS histories and outcomes](../../Silmaril/Process/LPS/Behaviour.lean)
· [TraceModels definitions](../../Silmaril/Semantics/TraceModels/Defs.lean)
· [Prefix and infinite-output lemmas](../../Silmaril/Semantics/TraceModels/Thms.lean)

## Institution for exact operational lowering

Fix `W`, `E`, `V` and the stopping tags once for the category. Use the
sequential runner with a fixed `e` for each test run. The runner steps a
`(tree, w)` configuration by observing its weak root. A return ends the
execution, a missing root silently self-loops, and a visible root takes
a kernel outcome and continues on the selected reply, or stops. With no
kernel outcome it is blocked. The test's observations carry finite public
log prefixes and tagged maximal outcomes. A terminal observation carries
the full accumulated log, also for infinite executions (finite or infinite
according to what the run emits). Request and ABI tags are available in
the syscall view. The institution below uses the common public view and
does not compare raw syscall records across signatures.

| Component | Definition |
| --- | --- |
| `Sig` | Objects are the request/reply signatures. An arrow `σ : Σ → Τ` sends `q` to `f(q)` and sends each `r : RespΤ(f(q))` back via `p(q,r) : RespΣ(q)`. Use identity maps and compose requests forward, replies backward. Equality is equality of those data with dependent transport. |
| `Sen : Sig → Set` | A sentence is a return type `A`, a test `t : Tree Σ A`, an initial context predicate `P(e,w)`, and an observation predicate `Q(e,w,o)`. Fix a universe for the tests. Translate the tree by replacing a request with `f(q)` and resuming its continuation on `p(q,r)`. Preserve return, divergence, `P` and `Q`. |
| `Mod : Sigᵒᵖ → Cat` | Models are kernels as above, initially in discrete categories. Pull a target kernel back by running it on `f(q)` and taking the relational image under the reply projection. Preserve the next store, output batch and stop tags. Model equality is pointwise equivalence of outcome predicates. |
| Satisfaction | `K ⊨ (A,t,P,Q)` iff for every `e,w` satisfying `P`, every observation of running `t` under `K` from `(e,w)` satisfies `Q(e,w,o)`. |

The tree map preserves identity and composition by the weak-root equations
and tree extensionality, or by uniqueness of a lawful fold when its
hypotheses are met. The kernel reduct laws follow by identity and
composition of relational images. For satisfaction, relate a source
residual to its translated target residual at the same store. On reply,
the reduct supplies exactly the images of target transitions and each
image has a target witness. Stops, empty outcome sets, returns and silent
self-loops agree. Induct on finite paths and match infinite paths one step
at a time (choosing a target witness at each stage in the lifting direction).
This gives equality of public observations, including the maximal tags,
and hence the satisfaction law

```text
K_T ⊨_Τ Sen(σ)(φ)   iff   Mod(σ)(K_T) ⊨_Σ φ .
```

`TypedSyscall.Signature.Hom`, `Action.push`, `Kernel.pull` and
`step_push_iff` are the existing single-step analogue. Their current
completion type covers return and exit. Extending the argument to the
additional stop tags and weak-tree runs is a proof obligation. The
`TypedSyscall.Linux` filling currently wraps the smaller `Process.Syscall`
read/write/exit relation. Reuse the shape of the transport proof for LPS
after supplying a typed adapter. The table above fits `Room`/`Corridor`
or `Silmaril.Inst.Plain` with discrete models. The ordered flat LambdaSSA
institution gives an existing weak-tree precedent for packaging a
satisfaction square. [Typed syscall transport](../../Silmaril/Process/TypedSyscall/Thms.lean)
· [Existing Linux filling](../../Silmaril/Process/TypedSyscall/Linux/Defs.lean)
· [Institution interface](../../Silmaril/Logic/Institution/Defs.lean)
· [Plain builder](../../Silmaril/Logic/Inst/Builders/Core/Defs.lean)
· [Ordered flat institution](../../Silmaril/SSA/Isotope/LambdaSSA/Semantics/ITree/Ordered/Flat/Institution/Thms.lean)

### Worked lowering and its scope

Take a test fixture with file `AB`, one read/write handle `f` at cursor zero,
and a private backed copy-out buffer `b`, with no interfering mutation.
For this profile resolve `f` to fd 3 and choose `b` as fixed interface
data. Lower `pread(f,1,1)` to the `pread64(3,b,1,1)` exchange. The target
response includes the typed decoding of the ABI return and the bytes
actually copied out. Project it to the high-level errno or byte string.
An impossible/malformed ABI completion in the adapter must be classified
explicitly before producing a typed reply. With raw return registers
alone, a pure reply projection cannot recover the read bytes. Lower the
subsequent `read(f,1)` to `read(3,b,1)` by the same convention.
Take the sentence that every maximal run returns the pair `(B,A)`,
allowing all finite prefixes. The proposed target fixture adapter delivers
`B` from offset one without changing the cursor, then `A` from cursor zero
and advances to one. Its reduct satisfies the source sentence and the
lowered test satisfies the target sentence. A handler that substitutes
ordinary `read` for `pread` in this fixture gives `(A,B)`, so the same
sentence fails on both sides for that target filling. This tests the
operational use of both the request map and the reply projection.

For an LPS bridge use `readSpecWith`/`writeSpecWith` and
`pread64SpecWith`/`pwrite64SpecWith` with the selected ABI's guards.
Relate the buffer contents and the effect's copy-out/write records to the
typed reply, and compare the descriptor cursor, file bytes and output
batch in the post-state. Use backed buffers, width/range bounds and a
non-append regular-file profile initially. For writes, require the matching
file-gap guard and read the actual copied prefix. For an independent
deterministic file handler, start with full available reads and accepted
writes under that fixture's bounds. An independently specified high-level
kernel still needs a simulation or equality proof against the LPS reduct.
[Regular-file read and write arms](../../Silmaril/Process/LPS/Sys/ReadWrite.lean)
· [Positioned arms and guards](../../Silmaril/Process/LPS/Sys/FsIo/ReadWrite.lean)
· [LPS state and syscall effects](../../Silmaril/Process/LPS/State.lean)

For streams, start from preconnected handles. A deterministic scripted
handler can consume the next bounded nonempty RX prefix, return EOF on FIN
at a positive count, and emit the chosen accepted prefix on send. For
example, on incoming `XY` followed by FIN, `recv(1); recv(2); recv(2)`
returns `X`, `Y`, then EOF. A reply counts acceptance by the local
endpoint. End-to-end delivery needs a peer model. LPS admits short sends
on the connected `sendto` path with `MSG_NOSIGNAL` and a null destination.
Use socket `read` for the restricted receive semantics. A socket
`recvfrom` or `recvmsg` arm in the existing model can report `unmodeled`.
A wrapper exercising those syscalls needs new coverage or an independent
adapter proof. Treat reset, timeout, and signal behaviour as profile clauses.
[Socket arms](../../Silmaril/Process/LPS/Sys/Socket.lean)
· [Socket read path](../../Silmaril/Process/LPS/Sys/ReadWrite.lean)
· [Network stream and end tags](../../Silmaril/Process/LPS/Stream.lean)

### Limits of the construction

State-dependent marshaling, many-step lowering, observation changes and
schedule changes require a larger construction. A two-call implementation
of one abstract call can expose an intermediate prefix or permit a
concurrent interleaving. To preserve satisfaction with those morphisms,
prove a commuting observation square in both directions, including
blocking, divergence and the contexts admitted by the profile. Atomicity
or an interference restriction and a prefix-respecting observation map
can supply parts of that proof. A one-way simulation usually transports
universal safety from a specification to a refining implementation. The
reverse implication in the satisfaction law can fail when the
implementation removes a branch that violates the sentence. A scheduler
that inspects concrete request syntax can also distinguish a test from
its translation. A scheduled extension needs a policy that commutes with
the residual relation.

There is no general inverse to kernel reduct. For example, if two ABI
responses project to the same reply, kernels offering only one of those
responses can have equal, nonempty reducts and empty intersection. On
unrestricted powersets of outcome facts the reduct is relational image.
It preserves unions and has a right adjoint, which admits each target
fact whose every source image is allowed. It can fail to preserve meets,
so a left adjoint to reduct on these inclusion orders is unavailable in
general. The powerset construction supplies no adjunction between
classes of deterministic or realistic kernels, which require separate
closure and existence proofs. In the discrete model categories used above,
an adjunction would require inverse object maps.

## Tree specifications and implementation conformance

For a fixed profile, context, and observation map, let `O(t)` be the set
of observations of a tree over the admitted runs. For sets `X` of trees
and languages `L`, ordered by inclusion, use

```text
α(X) = ⋃ { O(t) | t ∈ X }
γ(L) = { t | O(t) ⊆ L }
α(X) ⊆ L  iff  X ⊆ γ(L).
```

Thus `γα` closes a tree specification under all trees whose observations
are covered by the union. A spec is trace-closed in this sense iff
`γα(X) = X`, equivalently iff it is `γ(L)` for some language. For example,
“every observed send on the designated handle is at most four bytes” is
trace-closed when the observation retains call boundaries and lengths.
The corresponding statement need not be expressible over concatenated
bytes. Even with exact reply-indexed traces (which determine an individual
weak tree), unions forget which paths belong to one tree. Let a query
receive a Boolean and name a tree `tXY` for its two returned values
`X,Y`. The set `{tAA,tBB}` requires a constant answer across both
possible replies. Its trace union also admits `tAB`, so the spec is
outside the image of `γ`. This is a correlation across executions of a
single implementation, and union inclusion cannot prove it. In general
`αγ(L) ⊆ L` can be strict when a supplied language contains paths no
individual tree can realize within that language. Exact recovery is
restricted to languages that are unions of admitted tree observations.

Write a demonic implementation guarantee pointwise in the input and
environment. With a relation `R` between low and high initial states,
fix the observer(s), initial assumptions `P`, an environment coupling,
and an admitted policy class. A trace-level judgment has the form

```text
∀ input, e_low, e_high, w_low, w_high,
  P(input,e_low,e_high,w_low,w_high) → R(w_low,w_high) →
  ∀ admitted low policy π, ∀ low run ρ under (input,e_low,w_low,π),
    Obs_low(ρ) ∈ Allowed(input,e_high,w_high)
```

If `Allowed` is generated by high-level executions, membership gives
an existential high run in the related context for each observed low
run. It does not permit switching environments per observation. For
a tree-set spec require a witness high tree in the permitted set for
the entire family of runs at the scope of the contract (for example,
one witness across both replies to the Boolean query). Keep any
relational assumption across environments at that same scope. Safety
quantifies over every permitted short transfer, environment action and
admitted schedule. An angelic reachability statement instead asks for a
successful allowed run under a stated context. An implementation-controlled
choice in a mixed contract should be a causal strategy chosen before
demonic plays are quantified. “For every play there exists a favorable
choice” can allow foresight. For a must-return contract, require all
maximal runs under the declared fairness and readiness conditions to
return with an allowed result, and establish those conditions admit runs
in the intended deployment. Check UB freedom and absence of unsupported
steps under the asserted precondition, or state explicitly which tags
the contract permits. Erasing those tags from the output projection
cannot establish their absence.

## Implementation and proof checklist

- [ ] Define the indexed requests and typed errors with guarded handle,
  count and offset translation. Prove bound and frame lemmas for the
  relational file and stream steps and graph inclusion for each example
  deterministic handler. Cover positioned cursor preservation, ordinary
  cursor advance, short transfers, zero length and EOF.
- [ ] Give the sequential runner and labeled finite prefix relation. Prove
  nil, append and prefix closure, including pending and last-step inversion.
  Prove that projection to bytes preserves prefixes and define closure
  for cuts inside a batch. Exercise silent divergence, blocked calls,
  errno and unsupported execution as distinct cases.
- [ ] Give the shared-store scheduler runner and prove step correspondence,
  prefix equality and maximal-run correspondence for the singleton
  embedding. Use two readers of one cursor as an interleaving regression.
- [ ] Implement one guarded LPS adapter per family. Use
  `Process.Model.Defs` as a stable model entry, then the actual syscall
  arms and raw histories for arm-specific proofs. Prove decoder/footprint
  agreement and a two-way run bridge for the positioned-read fixture,
  with the socket-read coverage and guard restrictions explicit.
- [ ] Prove tree translation and reduct identity/composition, then the
  operational satisfaction square, including pending and divergent
  runs. Package it in `Room` or `Silmaril.Inst.Plain` and check the passing
  and failing file-fixture sentences. Keep institution packaging in a
  layer allowed to depend on both Process and Logic. The current Process
  region allows Semantics but has no direct Logic dependency.
- [ ] Prove the observation Galois connection and the query correlation
  counterexample. Discharge the explicit environment quantifiers for
  one file and one stream contract before claiming implementation
  conformance. [Process model header](../../Silmaril/Process/Model/Defs.lean)
  · [Region map](../../regions.toml)

Joseph A. Goguen and Rod M. Burstall, *Institutions: Abstract Model Theory
for Specification and Programming* (1992), §2.1, Definition 1. PDF SHA-256
`f6715ca333dd03dc153a65907c1c974fa151690bb94eafffc065c363265b634d`.
[PDF](https://courses.grainger.illinois.edu/cs522/sp2016/InstitutionsAbstractModelTheory.pdf)
· [DOI](https://doi.org/10.1145/147508.147524)
