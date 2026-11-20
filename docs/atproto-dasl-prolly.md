# Parameterized Prolly blocks over DASL

[The model](../Silmaril/Semantics/Prolly/Thms.lean) groups strictly ordered
entries bottom-up. A policy specifies a maximum width of at least two and a
level/key bucketer. There is no singleton cut; the last chunk may be short.
The builder stops as soon as the root fits. The checked results are lossless
flattening, common depth by construction, a width bound at every node, and
history independence for pointwise-equal finite maps. This is a worst-case
node-width guarantee, not a probabilistic balance or edit-cost result.

[`chunk_eq_iff`](../Silmaril/Semantics/Prolly/Cuts/Thms.lean) identifies
the unique partition with no skipped eligible cut. Only the final group
may end through input exhaustion without a cut. `CanonicalGrowth` lifts the
rule to all levels: only an over-width level can split, and the first level
that fits is the root. `build_canonical` and `CanonicalGrowth.unique` characterize
the builder independently of its fuel. These are abstract tree invariants;
local checks at a raw CAS node alone cannot validate them.

[The DASL adapter](../Silmaril/Formats/Dasl/Prolly/Thms.lean) instantiates keys
as byte strings in unsigned lexicographic order or signed 64-bit integers in
numeric order. With explicitly selected key and payload codecs, the profile
uses `["leaf", [[key, value], ...]]` and
`["branch", level, [[maximumChildKey, objectLink], ...]]`. Positive levels must
fit the signed profile; blob links are not valid child references. The
checked inverse is decode after successful encode, not an assertion about
all accepted syntax or canonical CBOR. This is not an ATProto MST format.

`Tree.observations` is the least relation of named blocks given a deterministic
bottom-up address function. `Stored` requires a successful shallow encoding
and the named binding at each block, not just compatibility with unrelated
observations. No hash injectivity is presumed. Equal semantic maps give the
same root name with the **same policy and fixed address function throughout**;
interchanging child names or choosing a different address can break this.
Raw-representation name uniqueness by itself is not this semantic guarantee.

[Root naming](../Silmaril/Formats/Dasl/Prolly/Root/Thms.lean) fixes the key
order, width/bucketer, recovered key and value codecs, partial renderer, and
an abstract `ByteArray → Option Name` oracle. A total `ByteArray → Name` is
the `some` case, available via `RootProfile.ofTotalHash`. It views a semantic
map as its lookup function. For
any ordered representation of that map, its set of admissible root names is
exactly `{root}` **iff** the bottom-up computation returns `some root`.
Successful naming requires encoding, rendering and a name at every
reached block, including children; `none` does not stand for an arbitrary
root or a default name. The checked builder supplies a bounded layout for
this profile. Other layout rules or value equivalences would need their own
coherence theorem; they are not implicitly identified with this profile.

Passing `Wire.render?` uses the existing DASL CBOR writer; this does not
prove a general CBOR roundtrip or renderer totality. The same canonical
bytes can have different names under different naming profiles. For a fixed
oracle the byte observations are a subset of its successful graph, not
necessarily the whole graph. `none` admits no pair. Determinism gives at most
one name per byte string under that oracle, not at most one byte string per
name. Collisions and binding remain separate. A binding
**shallow** store extension exists exactly when the union of the base and
the complete shallow observations binds. This theorem does not publish to a
raw store or guarantee that links inside user payloads are resolved. Store
binding and membership in a naming profile are independent requirements.
Any probabilistic collision or soundness bound would require a separate
explicit distribution on oracles or naming relations. None is used here.

[The closed-scan lookup](../Silmaril/Formats/Dasl/Prolly/Scan/Thms.lean) reads
all child occurrences with fuel. It checks declared levels, arity and width,
child separators, and strict key order across the concatenated leaf entries.
Missing data, invalid wire, invalid node, and fuel each give a distinct error;
only a completed scan can return absence. The proof relates every successful
answer to **any** binding reference containing the successful reads and the
canonical stored tree. It applies unchanged to such binding extensions.
The reader reuses the `Wire.ReadResult` interface; it does not reparse CBOR or
authenticate raw byte sources by itself. Local validation does not establish
canonical chunking for an arbitrary store. The theorem uses a canonical
reference witness; it does not assert every input has one.

[Routed lookup](../Silmaril/Formats/Dasl/Prolly/Route/Thms.lean) visits only
the first child whose inclusive upper bound covers the key. The builder
provably has strictly ordered leaf entries and truthful child maxima,
including on recursively lifted chunks. These global invariants justify
skipping siblings, even unreadable ones, and returning absence beyond the
last separator. A missing selected child is never absence. The checks on
the visited path do **not** certify an arbitrary root: negative and positive
soundness both require a rooted representation in the binding reference.
`routedLookup_build_sound` makes the two inclusion hypotheses explicit:
the reference must include the stored tree and the successful reader
observations. It does not need unique names.

## Follow-up

- Prove a declarative canonical-cut characterization and sufficient-fuel
  completeness for routed lookup against a fully supplied canonical store.
- Add update/admission proofs: successful updates preserve all old bindings,
  reject collisions, and do not rewrite missing or invalid blocks. Connect
  address derivation to a checked serializer and fixed hash on successful blocks.
- Model ATProto MST separately: SHA-256 two-bit-group layer rule, canonical
  longest prefix compression, exact `e` / `l` and `k` / `p` / `t` / `v` node
  shapes, and child intervals. A routed negative requires a valid interval and a
  checked terminal or absent edge; a missing child cannot certify absence.
