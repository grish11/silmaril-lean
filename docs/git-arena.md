# Git arena: local bindings and reads

`Silmaril.Formats.Git.Arena` specializes the finite slot model in
[arena foundation](projects/arena-foundation.md). A hole is not a placeholder;
a placeholder can claim a native Git OID or an abstract CAS name without
asserting the presence or identity of a payload. Native OIDs have disjoint
SHA-1 and SHA-256 tags and exact widths. A slot can record a kind hint, and a
typed Git read checks known hints and the kind of a returned payload. CAS
names are in separate raw and object lanes, even if both use the same name
type. A payload may be inserted without either kind of name. In particular,
the profile can classify a Git-less tree as a tree even if an OID cannot be
derived for it.

| Operation | Meaning |
| --- | --- |
| `step (.insert payload)` / `step (.reserve id kind)` | Claim an empty key with bytes or with a name, independently. |
| `step (.attach id kind)` | Add a claim without removing earlier claims; refine an unknown kind without replacing a known kind. |
| `step (.materialize payload)` | Fill a placeholder or confirm an identical resident payload. Check every claim at the slot. |
| `assign lane` | Serialize a resident payload and compute a name for that lane, if both operations are available. There is no inverse hash. |
| `cache key id reader` | A claimed resident key is a hit, without consulting the reader. At a claimed placeholder the reader can return missing, deferred, invalid, conflict, or a candidate payload. Candidates go through `materialize`. |
| `readGit` / `readCas` | Resolve aliases by agreement and serialize the resident value in the requested lane. Unindexed, placeholder, wrong kind, conflict, and unavailable wire encoding are distinct. |

`Profile` chooses a native serializer and hash separately from a canonical
CAS serializer and naming function. `nativeObjectBytes` uses the existing
[native Git subset](git-translation.md), returning no bytes for an opaque
reference. Git and CAS computation can fail independently. A computed name
mismatch cannot be overridden. When computation is unavailable, `attest` is
an explicit, caller-supplied validation hook (default off). The arena assumes
neither stated algorithm is injective or collision-resistant. In a shallow
clone a reader can explicitly defer a placeholder. A local unindexed result
is not proof that a remote object is absent.

`step_spec` exposes the local update and frame, `valid_step` preserves validity,
and `step_extends` preserves every prior claim, kind hint and resident value.
`observed_binding` is functionality of the *admitted observations* even with
alias slots. Conflicting resident values or known kinds for one ID cannot be
published. Two verified derivations of different names in the same profile
and lane imply unequal payloads; two matching asserted OIDs do not imply
equal payloads. A name-first and a content-first insertion commute when both
complete. Cache success refines the state and supplies an observed binding;
`observed_refines` states exactly what a trusted reference relation must
justify about derivations and external attestations. `readWire_found`
requires actual resident content and successful serialization. The
[discard codec view](projects/arena-codec-views.md) keeps claims while recording
unencodable slots as rejections; it does not certify bindings in the new
representation.

The finite scan and pairwise agreement check are a specification, not an
indexing or interning algorithm. Equality is equality of the chosen payload
type, not an extensional quotient of differently represented payloads. The
public [Covalence CAS trait](https://github.com/hiloopai/covalence/blob/5890a5fba9f76a850705abe40048f50f0b2541cf/crates/cas/trait/src/lib.rs)
similarly separates unchecked reads, vouched-for reads, and checked facts;
its [Prolly loader](https://github.com/hiloopai/covalence/blob/5890a5fba9f76a850705abe40048f50f0b2541cf/crates/cas/prolly/src/io.rs)
checks path and node shape above CAS. These are design references, not
implementation, wire-compatibility or Rust refinement claims. This slice
does not fix a BDASL BLAKE3 filesystem profile or implement import/mount.

Run the standalone regression and theorem axiom audit:

```sh
lake build --wfail Silmaril.Formats.Git.Arena.Thms
lake env lean -DwarningAsError=true --run tests/formats/GitArena.lean
make check CHECK_TARGETS=+Silmaril.Formats.Git.Arena.Thms
```

The regression deliberately uses a colliding abstract function to exercise
rejection instead of implicitly treating the name as proof of equality.
