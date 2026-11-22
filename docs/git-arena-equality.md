# Git arena: equality admission and replay

`Silmaril.Formats.Git.Arena.Equality` adds a read-only equality overlay to
the [coherent arena](git-arena.md) and [Git OID provenance index](git-oid-collision.md).
It does not change arena slots, CAS lookups, or Git collision policy. A replay
filters original, provenance-tagged requests into edges. `Related` is their
undirected equivalence closure over slot keys. It is useful as an admission
contract for a future equality structure, not a congruence/rebuild algorithm.

| Evidence | Required for admission on two resident endpoints |
| --- | --- |
| `content` | Decidable equality of actual typed payloads; no identifier required. |
| `canonicalCas lane name` | The same lane/name is actually claimed with resident content at both endpoints, both deterministic derivations produce it, and the soundness proof uses the arena's coherent observed binding. Two independent computations of the same digest do **not** themselves justify equality. |
| `nativeBytes oid` | An unblocked, unique observed preimage and endpoint encodings equal to those exact bytes under a recovering codec. Both algorithms use the same rule. |
| `trustedGit oid` | SHA-1 has no label-trust route. SHA-256 requires an explicitly configured authority, an unblocked unique preimage, and authority validation for that tagged name, exact preimage, and both payloads. Functionality of that validation relation is a supplied proof, not a consequence of the digest tag. |

The checker rejects even an asserted matching Git OID if the two actual
canonical derivations give different CAS names in a **single fixed profile
and lane**. It never compares across unrelated profiles or raw/object lanes.
`derived_different` proves the semantic disequality; it uses determinism,
not hash injectivity. `related_reject_different_cas` rules out reaching the
same pair indirectly through a chain of admitted edges. An absent derivation
does not establish either equality or disequality. Holes and shallow
placeholders cannot seed; this checker never fetches or materializes them.

`check_sound` proves an accepted edge has two resident witnesses for the same
typed payload in a coherent arena, and `related_content` extends that to the
whole closure. `related_typed` preserves typed serialization/decoding
observations; `related_readWire` connects such a resident to bytes read
through an existing observed name, without attaching its claim to another
slot. OID-based admissions require a unique hit (`check_oid_hit`); for an
index valid under the chosen verifier, `check_oid_verified` gives the exact
verified preimage. Neither parsing nor a digest label alone supplies trust.

## Snapshot and live operation

- **Pinned snapshot.** Freeze arena, profiles, observed OIDs and authority,
  including the dispute view. Growing only the request log is monotone.
  This does not imply monotonicity when any of those inputs changes.
- **Live overlay.** Apply a new provenance snapshot, deliver collision
  notices with `deliver` (strict rejections included), and mark explicit
  authority revocations with `revoke`. Recompute from the original requests,
  not the old accepted edges or union-find classes. Delivered disputes,
  revocations, and ambiguity all exclude that OID's dependent edges, while
  `check_nonOid_frame` preserves independent content/CAS admissions and raw
  CAS reads remain unchanged. Independent surviving evidence may still
  connect the same endpoints; revocation invalidates the justification, not
  a fact proved by unrelated evidence.
- **Publication boundary.** A live consumer must serve only the rebuilt view
  of a current authoritative snapshot that has received its notices. Freeze
  or fail closed on OID-backed answers across a delivery/rebuild gap. The
  specification does not prove race-free notice delivery or deletion from an
  already-merged mutable e-graph.

## First implementation recommendation

Start with **strict committed bindings and a separate diagnostic-retention
seam**. Keep verified collision candidates out of the authoritative store;
retain them only in a diagnostic view that cannot resolve Git reads or seed
equality. Deliver its dispute notices before serving affected live OID-backed
answers. This preserves atomic rejection and stable independent CAS reads
without hiding detected collisions from equality consumers. Until reliable
publication and replay are in place, serve a pinned snapshot or disable
OID-backed equality in live views. Keep SHA-256 authority opt-in, and do not
enable a SHA-1 label shortcut.

The Lean layer depends only on the Git arena and collision-policy stack
(#1579 and #1593); it does not depend on the open generic e-graph stacks,
the routed filesystem, or a choice of canonical directory layout. The
regression uses deliberately colliding SHA-1/SHA-256 oracles and synthetic
BLAKE3-shaped CIDv1 names, not real cryptography. It also exercises direct
nameless equality, distinct admitted CAS names with identical unchecked Git
claims, a shallow placeholder, notices, revocation, and unaffected raw reads.

```sh
lake build --wfail +Silmaril.Formats.Git.Arena.Equality.Thms
lake env lean -DwarningAsError=true --run tests/formats/GitArenaEquality.lean
make check CHECK_TARGETS=+Silmaril.Formats.Git.Arena.Equality.Thms
```
