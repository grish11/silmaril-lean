# Actual cJSON_GetArraySize bounded traversal

The unchanged cJSON 1.7.19 function is projected from the already-saved public
translation unit used for the predicate bindings. `size_t`, the actual cJSON
struct and the complete function are exact TU spans, joined with newlines;
source is not rewritten to avoid assignment, increment or the while loop.
The original upstream function span is separately pinned. This reuses saved
preprocessing evidence; it is not a new preprocessing, exporter or artifact
build, and historical image/header identity and whole-TU adequacy remain unproved.

Actual pinned Cerberus elaboration produces one Core procedure and no globals.
The needed equations are from Cerberus b3e11ea334e95359907d4abf9194f0e7fedc6c6a:
[postfix update](https://github.com/rems-project/cerberus/blob/b3e11ea334e95359907d4abf9194f0e7fedc6c6a/frontend/model/translation.lem#L663),
[assignment](https://github.com/rems-project/cerberus/blob/b3e11ea334e95359907d4abf9194f0e7fedc6c6a/frontend/model/translation.lem#L2404),
[pointer initialization](https://github.com/rems-project/cerberus/blob/b3e11ea334e95359907d4abf9194f0e7fedc6c6a/frontend/model/translation.lem#L4083)
and [SeqRMW](https://github.com/rems-project/cerberus/blob/b3e11ea334e95359907d4abf9194f0e7fedc6c6a/frontend/model/core_aux.lem#L540).
Fresh-symbol/evaluation order, annotations, negative assignment store,
unsigned wrapping, unspecified-value branches and actual allocation/lifetime
operations are retained. No substitute body, source callee or desired-refinement
law is supplied. Atomic/CHERI/floating/pointer-postfix branches are not promoted.

The canonical existing x86-64 ELF function is35 bytes at0x4090, with actual
dynamic symbol and CodeAt facts. Its signature has one cJSON pointer argument and a signed-int return; its
private machine stack footprint is0 bytes: all target memory/mapping state must
be preserved. The result is observed as signed EAX low32 bits.

The contextual domain is null plus acyclic list lengths0..64. The64-node bound is
an intentional finite demonstration, below both size_t wraparound and the
source's documented narrowing-to-int overflow case. It is not a full-input
claim. The caller root and each node have distinct, correctly aligned64-byte
allocations, with initialized child(offset16)/next(offset0) pointers and real
allocation provenance. Caller objects are readonly. Source parameter/local
objects are private, with actual creation, stores and kills; the initial source
allocation region is disjoint from the caller heap. Caller allocation/byte/
pointer-provenance/lifetime state, registrations and stdout are observable.
Private automatic-allocation bookkeeping and diagnostic location updates are
explicitly outside the source observation.

No result/count or termination premise appears in entry conditions. The
UNPROVED obligation demands joint entry existence, Core safety, machine first
return, ABI preservation, preservation of all machine memory and a matching
finite Core execution/observation. It does not state universal source termination,
divergence equivalence, cyclic-list correctness or behavior on oversized/invalid
lists. Outside-lifetime pointer access still has an explicit unsupported UB
mapping in the imported memory implementation; this is outside the chosen valid
allocation domain and is not relabeled as a completed C UB diagnosis.

Finite actual-Core regressions cover null and every length0..64, readonly caller
heap/provenance preservation, and allocation/killing of both automatic locals.
The missing-allocation negative test retains its precise unsupported
classification. These executions are neither a contextual nor termination proof.
All corpus refinements remain UNPROVED;0 semantic proofs are claimed.
