# Native Git to DASL name correspondence

[`Git.Translate`](../Silmaril/Formats/Git/Translate/Defs.lean) interprets a
finite, typed Git object unfolding twice. On the source side, the [native
profile](git-native.md) serializes the loose-object preimage, and its independent
assignment names those bytes. `NameBytes .sha1` and `.sha256` give the two
native OID widths; the library does not fix a hash implementation. On the
target side, the [DASL layout](git-dasl.md) and commit metadata codec produce
shallow object values and raw blobs. `Wire` separately specifies a possibly
partial object serializer and two byte-naming relations (object and raw).
For canonical ATProto DASL use `Formats.Dasl.Wire.Serializes`; `Wire.ofFunctions`
can instead state agreement with a supplied writer and byte-to-name functions.
The test uses native SHA-1 or SHA-256 and DASL CIDv1 with SHA-256.

`translate` takes an already typed `Object`, not a native OID or repository. It
computes child names before directories and tree/ordered parent names before
each commit. Shared occurrences are evaluated again rather than memoized;
`Audit.sharing` requires them to agree on the target for each `(kind, source)`.
Nothing requires distinct source names to get distinct target names. Prolly
blocks are in the target store and must satisfy the same byte-naming contract;
they do not represent native Git objects and do not get native-name pairs.

Reference cuts (ordinary subtree/parent refs or external gitlinks) are accepted
only when an explicit kind-aware frontier map supplies a target name; a missing
mapping rejects the fold. An accepted cut supplies no bytes or availability
evidence. `Trace.Closed` means no cuts, and `Audit.frontierAllowed` can instead
restrict permitted pairs for a partial view. The policy is by kind and name,
not by edge role; e.g. a commit OID allowed as a gitlink is also allowed as an
opaque parent. Use a closed unfolding when no cuts are permitted. The inductive
input rules out recursive structural cycles; an opaque reference can hide a
cycle, so a successful partial fold is not evidence of acyclicity.

## Checked claims

- `translate_native`: for any successfully translated finite unfolding, the
  independent native renderer yields the same root name. For an expanded object,
  its exact preimage is in the trace; for a reference, the trace records only
  its frontier pair. Changing the target layout or namer cannot change the
  source name or preimage if both translations succeed.
- `translate_commit_evidence`: for a successfully translated commit constructor
  with an `Audit`, its tree and ordered parents are paired with their translated
  names. The exact native commit preimage must occur at the source name in the
  caller's source observations and satisfy the native naming relation. The
  target codec recovers the mapped tree, ordered parents and selected metadata;
  the encoded commit is present in the target store with a serialization and
  target naming witness. `Audit.sameTarget` is the sharing guarantee for
  repeated same-kind names in that trace.

An `Audit` is supplied evidence, not an executable checker. Source-byte
agreement is separate from using a canonical target writer; no claim equates
the native and DASL digests, or says that the target metadata codec recovers
native bytes or fields it chose not to encode.

## Rooted partial stores

[`Git.Translate.Graph`](../Silmaril/Formats/Git/Translate/Graph/Thms.lean)
starts at a typed native address `(kind, name)` and takes a pure, partial
lookup returning a typed shallow node and its original loose-object preimage.
The adapter distinguishes absent from invalid data (including kind mismatch);
the walker also checks that the restricted native writer reproduces the exact
bytes and the native name function returns the requested name. No parser or
on-disk Git adapter is assumed. Source and DASL names and naming functions
remain independent.

Discovery is depth-first, reading a commit's tree before its parents, in list
order, and visiting tree keys in key order. It checks for an active-path cycle
before memo or fuel checks and reuses completed plans by typed address. Fuel
bounds the depth of **uncached local expansions**, not the number of edges or
objects: a completed-plan hit works at zero fuel. An exhausted walk reports
the next uncached address; it does not rule out a missing binding or a deeper
cycle. It reports the first encountered failure and returns no partial plan.
A gitlink is always external, even if that commit name also exists locally;
it requires an explicit `.commit` frontier mapping and consumes no depth.
The same name on a parent edge must resolve locally, regardless of frontier
entries. A gitlink is never evidence that the other repository is available.

- `Plan.reaches` covers every finite local path; `Plan.accessible` certifies
  that local edges below a successful root are well-founded. `Plan.native_exact`
  regenerates the original bytes at local roots, retaining native names on every edge.
- `Outcome.rootPair` relates the requested typed root to the target root.
  `Outcome.reaches` gives a materialized target pair and exact observed native
  preimage for **every** reachable local address, not an opaque pair.
- `Graph.run` checks native preimages and source naming, frontier permissions,
  and functional same-kind sharing across the finite trace. `Outcome.audited`
  combines these checks with a separate `Wire.Agrees` witness for the target
  store (including auxiliary Prolly blocks). It does not assert that arbitrary
  layout/serializer/namer combinations agree, or that every finite valid store
  succeeds at any particular fuel. `Outcome.commitEvidence` connects the
  target codec and wire witness to the source commit's actual ordered parent slots.

Discovery memoizes reads and plans, not the bottom-up rendering: the existing
fold expands shared occurrences and the trace audit currently compares pairs
of distinct events. The next steps for production use are an adapter for the
supported native bytes, memoized target rendering, and enumerable target-block
validation for specific serializers/layouts.

## Checks

```sh
lake build --wfail +Silmaril.Formats.Git.Translate.Graph.Thms +Silmaril.Formats.Git.Native.Thms \
  +Silmaril.Formats.Git.Dasl.Layouts.Thms +Silmaril.Formats.Dasl.Wire.Defs \
  +Silmaril.Crypto.SHA1.Thms +Silmaril.Crypto.SHA256
lake env lean -DwarningAsError=true --run tests/formats/GitTranslate.lean
```
