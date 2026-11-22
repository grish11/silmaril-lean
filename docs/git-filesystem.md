# Git trees as BDASL filesystem snapshots

The reference contract is **expanded Git tree → stage → CAS publish →
read by tree CID**. No commit or native OID is needed to read a published
snapshot. The source is the [typed Git model](git-translation.md), not a
loose object, pack, or checkout parser. Future ingestion may resolve native
objects via the [arena](git-arena.md) before presenting an expanded tree.

## Fixed profile

- Raw blocks use CIDv1 `01 55 1e 20` followed by a 32-byte digest. Directory
  blocks use `01 71 1e 20`. The supplied pure function stands for BLAKE3; Lean
  checks the envelope and exact bytes used, not the hash implementation or
  security. Original SHA-1/SHA-256 addresses are distinct from these CIDs.
- Directories use the landed Git `{mode, link}` entry codec, the Prolly byte-key
  block codec, unsigned lexicographic byte order, width 32 and width-only cuts.
  The fixed BDASL wire profile serializes the blocks. Child and auxiliary
  block names are computed bottom-up. This is a versioned choice in this
  specification, not a claim of matching any Rust Prolly wire profile.
- Byte components reject empty, dot, dot-dot, slash and NUL. Other bytes,
  including non-UTF-8, are kept. The String façade uses exact UTF-8 only; it
  does not claim that a non-UTF-8 entry has a String spelling. Use the raw
  path for such entries. Modes distinguish regular and executable files,
  symlinks and directories. Symlinks return their target bytes but are not
  followed. Gitlinks, unresolved refs and commits are explicit import faults
  in this tree-only profile.

## Admission and reads

`stage` can fail if a component is unsupported or any codec fails to emit.
On success, `names_iff` states existence and uniqueness for any relation
that covers the emitted root bytes and is contained in the graph of the
same fixed addressing function. It does not establish universal serializer
totality. `publish` is pure admission against an authoritative byte snapshot:
equal writes are reusable and different bytes at the same name conflict.
The returned snapshot binds precisely the old and staged bytes. The staged
image is indexed by its hash parameter, so the root cannot be rehashed under
a different profile while keeping stale child addresses.

`locate` takes an immutable tree CID and a byte path. An empty path is a root
descriptor, not an availability assertion. A positive directory read checks
the caller's bytes against the requested CID before parsing, then does a
bounded closed Prolly scan. `.ok none` is absent in the completed directory;
missing, deferred, invalid and conflicting blocks and fuel exhaustion are
not absence. `lookupChild_sound` gives exact entry recovery (or absence)
under the canonical `Stored`, binding and reader-inclusion hypotheses;
hash comparison alone does not supply those hypotheses. The same `Store`
interface accepts a published snapshot or the arena's read-by-CAS-name view.

`locate` is still the closed-scan reference. `locateRouted` uses the verified
on-demand reader; `locateResident` captures an explicit set of names and uses
the same routing algorithm. Under the same rooted binding reference, both
routed modes refine the directory map and agree with a successful scan. A
routed success need not imply scan success: an unrelated unread sibling is
required by the scan but not by the route. A missing selected block, invalid
wire, or exhaustion stays an error. Fuel bounds Prolly block depth per
component, and the finite path bounds directory descent. This does not
implement FUSE or by itself certify the reference supplied by an import.

```sh
lake build --wfail Silmaril.Formats.Git.Filesystem.Routed.Thms
lake env lean -DwarningAsError=true --run tests/formats/GitFilesystem.lean
make check CHECK_TARGETS=+Silmaril.Formats.Git.Filesystem.Routed.Thms
```

The executable fixture checks a nested executable with basename `ff` (one
byte in hex), a symlink to it, absence vs. deferred fetch, conflict rejection,
and byte/mode readback through both backings. The default run uses a test
function. To use real BLAKE3 **outside Lean**, pass a path to `b3sum` following
the test filename. The fixture iterates an external digest table until every
block in the final staging has an external digest; functions outside the
fixture domain remain abstract. The table harness is not a production hasher.
