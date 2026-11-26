# Finite handled ITree trace predicates

`Silmaril.Logic.ITree.Institution.Trace.Thms` exposes `TraceInstitution.institution`,
a `ClassicInstitution` over `TraceSignature`. It uses the same weak trees,
relational handlers and discrete model categories as the
[return institution](itree-institution.md). A sentence specifies a program and a
predicate on its entire finite observation. Each observation records the typed
request and actual reply of every completed exchange. It ends in an
uninspected prefix, a visible pending request, or a return. Satisfaction checks
every such observation from every initial state.

## Signature arrows and exact image

A trace arrow wraps a `Signature.Hom`. It embeds packed requests (the event with
its reply type) and requires a bijection for each backward reply function. The
forgetful functor to `Signature` supplies the existing model reduct and its
identity and composition laws. The reduct keeps the target state space and
initial-state predicate. A legal source step has a target step at the mapped
request whose reply projects to the source reply.

The tree translation uses the backward reply function in each continuation.
`TraceSignature.Hom.trace` uses its inverse to send a recorded source reply
forward. The inverse is obtained noncomputably from bijectivity. Results are
unchanged, and translating a pending request only maps its packed request.

`TraceSignature.Hom.handledTrace_image` holds for every target observation and
every state. The observation is admitted on the translated tree exactly when
it is the image of a source observation admitted by the reduct. Reflection
recovers the visible source node from the translated tree's destructor. At
an exchange, the target step supplies the reduct witness and reflection
continues along the corresponding source continuation. Pending requests require
no handler step. The forward direction uses the reduct's step witness and
reply bijectivity to recover the exact target reply.

Sentence translation takes the direct image of the predicate. In particular,
a target observation with no source preimage is rejected. `Sentence.translate_id`
and `Sentence.translate_comp` give equality of whole sentences. The latter
uses `Sentence.accepts_translate_comp` on every target observation, including
those outside the image. `satisfaction_at` gives the satisfaction equivalence at
each state, and `satisfaction` quantifies it over the model's initial states.

## Why the arrow restrictions matter

The exact-image proof itself uses no request injectivity. The source tree
identifies the current request during reflection. Injectivity is used for
satisfaction with arbitrary predicates and direct-image translation. Suppose
two distinct source requests map to the same target request. A source program
can expose the first request with a handler offering no replies. A predicate can
accept the prefix and the second pending request while rejecting the first.
The translated predicate then accepts the actual target pending request via
the second request's preimage, even though that preimage is unreachable in the
source. Packed request injectivity rules out this collision for pending requests
and, with reply bijectivity, for complete observations.

The wider return institution can feed arbitrary backward reply functions to
continuations because it only compares return values. If a backward function
identifies two distinct target replies, a handler can admit both and give two
different target exchange traces over the same source exchange. A single
forward trace could not cover both. If a source reply is omitted by the backward
function, it has no target inverse at all. Reply bijectivity supplies the
single-valued inverse used here on every typed observation. A relational
translation would require its own predicate translation and satisfaction laws.
Disjoint effect inclusions are trace arrows, so target requests need not all
come from the source.

## Checked heap and clock examples

`Silmaril.SSA.Isotope.LetIter.Heap.Institution.Trace.Thms` uses the actual LetIter
heap handler and the shared heap-plus-clock model.

- `sat_rename` transports an arbitrary heap trace sentence along a pointer
  equivalence. `rename_alloc_trace` shows the new pointer in an allocation reply
  and in the subsequent pending read.
- `noClock_of_handledTrace` rules out both pending and completed clock operations
  in every observation of a heap program included into the combined signature.
  `same_return_different_history` exhibits a translated heap allocation and a
  translated tick that both return unit after one exchange from the same initial
  state. The no-clock predicate distinguishes their observations.
- `alloc_full` characterizes all observations of a single allocation attempt on
  a full store. It admits the empty prefix and the pending allocation request,
  with no completed exchange or return.

This profile covers finite weak observations. Pending means that the request is
visible at the observation boundary, whether or not the handler could answer.
The observation type has no separate outcomes for fault, refusal or exhaustion,
and expresses neither infinite behavior nor concurrent scheduling.

```sh
lake build --wfail \
  +Silmaril.Logic.ITree.Institution.Trace.Thms \
  +Silmaril.SSA.Isotope.LetIter.Heap.Institution.Trace.Thms
```

The public theorem roots import the proof implementations and the checked
examples. The existing `Silmaril` library globs cover them for both full and
scoped CI builds.
