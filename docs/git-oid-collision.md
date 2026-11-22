# Git arena: OID collision policies

`Silmaril.Formats.Git.Arena.Collision` layers a Git OID observation index over
the [coherent arena](git-arena.md). Disputed Git candidates are not conflicting
resident bindings in that arena. Set `Policies` independently for each
tagged OID algorithm; neither the SHA-1 nor SHA-256 tag gives a collision or
trust guarantee.

`Verifier` takes exact *uncompressed native preimages* (header and payload),
not a canonical re-encoding of an imported object or naked blob content.
Admission checks structural validity at the caller's native-format boundary.
Only an admitted preimage with an available, matching digest enters the
index. `verified_iff` gives this specification. The oracle and validator are
supplied by the adapter, and validity and trace statements refer to one fixed
verifier. The proof uses neither hash injectivity nor inverse hashing.

| Input | Result |
| --- | --- |
| OID-only claim | Create an unverified placeholder if vacant; never add a candidate or demote a verified bucket. |
| Transient missing fetch | Report `.missing`, without changing the index or learning that an object is absent. |
| Malformed native bytes | Report `.malformed`, without hashing or mutating the index. |
| Digest unavailable / differs | Report `.unavailable` / `.mismatch`; these are not collisions, and neither modifies the index. |
| First verified preimage | Set the incumbent and expose a unique hit. |
| Already-observed exact preimage | `.duplicate` is idempotent, including an alternative in a disputed bucket. |
| Verified, distinct preimage at an occupied OID | Strict rejects atomically; retention records an additional candidate without replacing the incumbent and exposes `.ambiguous`. |

**Checked guarantees.** `step_strict_collision` returns the original store,
not just the old queried value. `step_retain_collision` gives the exact new
bucket and `query_retain_collision` gives its ambiguous result. The incumbent
is diagnostic in `.ambiguous`, not a preferred hit. `step_extends` prevents
candidate loss and incumbent replacement, `step_frame` preserves other OIDs,
and `no_hit_after_dispute` prevents a unique hit from reappearing in an
extension that preserves both distinct candidates. `run_valid` preserves
verified, duplicate-free candidates. `run_agree` compares any two policy
configurations: on a collision-free trace they produce identical outcomes
and final indices. The premise tests verified input against the incumbent
along the retention reference run, not against a claim of cryptographic
strength.

Use `Store.git.query` for policy-governed Git reads; the lower-level arena's
slot claims are not a fallback for a disputed OID. Git events do not create
or hide independent raw CAS bindings: `step_cas` and `step_readRaw` prove that
the CAS state and reads are unchanged. Publishing a candidate under a CAS
name is a separate checked CAS operation. Strict rejection leaves the
incumbent readable in the committed Git snapshot; its rejection notice is
separate from that snapshot. A consumer can suppress such a read by
consulting its dispute view first.

## Equality and changing trust

`canSeed` requires a nonblocked unique hit and both endpoints encoding to
those **same exact bytes**. Merely sharing an OID, even with available digest
computation, is insufficient. Start from a valid index (e.g. `empty` plus
checked events). `canSeed_iff`, `seed_refuse_nonhit` and `seed_refuse_blocked`
specify what is permitted; `seed_sound` additionally requires a recovering
codec at the endpoints. An unverified, ambiguous or externally blocked label
cannot authorize a seed. For strict rejection, `Disputes.record` latches the
notice outside the committed store. `record_blocked` and `record_preserves`
show how to make a live view fail closed even when the strict committed
snapshot still returns an incumbent.

An equality proof from actual recovering preimages does not become false
when a collision is later observed. Its *authorization as an OID-backed
seed* can nevertheless expire. Pin the index, verifier and dispute view for
immutable snapshot consumers. A live union-find/e-graph cannot merely reject
future merges and keep stale OID-backed answers: retain seed provenance and
rebuild/revalidate the dependent view, or suspend those answers until it is
rebuilt. Deliver strict rejection notices to that view before serving live
answers; dropping a notice loses the dispute information not in the strict
store. This is a checked seed interface, not a persistent e-graph or a
transactional notice-delivery implementation.

## Choosing a policy

| Need | Candidate policy | Trade-off |
| --- | --- | --- |
| Preserve committed state on a conflicting observation | Strict | Keeps the incumbent; live trust consumers must ingest rejection notices. |
| Keep both verified preimages for inspection | Retain | Explicit ambiguity; extra storage and no unique Git hit. |
| Allow existing independent CAS consumers to continue | Either | No Git event changes the CAS lane; independent CAS checks still apply. |

Apply the matrix separately to each algorithm's operational trust zone. This
specification does not pick a default. It does not implement native parsing,
real SHA, persistent storage, or live e-graph invalidation.

```sh
lake build --wfail +Silmaril.Formats.Git.Arena.Collision.Thms
lake env lean -DwarningAsError=true --run tests/formats/GitOidCollision.lean
make check CHECK_TARGETS=+Silmaril.Formats.Git.Arena.Collision.Thms
```

The standalone test runs both policies for both widths using synthetic
colliding oracles and prints the public theorem axiom dependencies.
