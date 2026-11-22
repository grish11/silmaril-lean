# Bounded Git filesystem readback

This is a proof slice on top of the [fixed Git filesystem profile](git-filesystem.md).
It does not change the writer, CID envelope, directory format or scan reader.

- `BlockBounds` checks the positive signed-i64 branch level and the exact
  BDASL CBOR model: matching link tags, `Value.Encodable` (wire argument and
  length bounds), and canonical map order. `bdasl_roundtrip` gives successful
  serialization and recovery of that same shallow block under those checks.
- `DirectoryBounds` applies the block condition to the built directory with
  already assigned child CIDs and any well-tagged object fallback. Under the
  condition the writer succeeds and no reached block uses a fallback.
  `stageDirectory_of_ok` also records the exact bytes and names in any
  successful directory image, independently of parser recovery.
- `StageBounds` checks valid byte components, excludes opaque references and
  gitlinks, and applies the directory condition after staging each child.
  `stage_of_bounds` then gives an image for every bounded tree. This is not a
  theorem that every native Git repository satisfies the stated bounds.
- `Image.readbackPublished` establishes recursive readback at the image tree
  CID: exact byte-key directory queries at sufficient per-directory fuel,
  preserved edge modes and kind-specific child names, and exact raw blob
  payloads. The result needs no source Git OID. An alternative authoritative
  fetch can use `readback_of_stage` with exact coverage of `image.writes`.

Publication is a separate premise. Staging computes a unique root preimage
for the fixed layout and abstract digest; it cannot promise no collisions.
Equal writes are reusable, and unequal bytes at the same CID must fail
admission. The readback theorem concerns a complete published observation;
it never turns a failed fetch into an absent path in a partial observation.

```sh
lake build --wfail +Silmaril.Formats.Git.Filesystem.Writer.Readback
lake env lean -DwarningAsError=true tests/formats/GitFilesystemReadback.lean
make check CHECK_TARGETS=+Silmaril.Formats.Git.Filesystem.Writer.Readback
```
