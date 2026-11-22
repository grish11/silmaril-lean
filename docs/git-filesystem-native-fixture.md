# Native Git to BDASL fixture

`git_filesystem_native.py` creates fresh bare SHA-1 and SHA-256 repositories.
It writes the same two trees and blobs through Git plumbing, reads their raw
payloads with `git cat-file`, and recomputes every native object ID over the
Git kind-and-length header and payload. There is no commit dependency.

Lean checks the exact two exported tree bodies against the landed native
Git serializer, including the original child OIDs, the raw basename `ff`,
executable mode, and symlink edge. The exported blob bytes are the input to
staging. Both Git formats must produce the same target CID, with final block
digests supplied by external `b3sum`. The existing tests then mount using
only the tree CID and a CAS reader, on both the published map and arena.
There is no lossy UTF-8 conversion or implicit symlink following.

The script generates witnesses for this known tree shape. It is not a Lean
Git parser, general native importer, or production hash implementation.

```sh
lake build --wfail +Silmaril.Formats.Git.Filesystem.Routed.Thms
python3 -I tests/formats/git_filesystem_native.py "$(command -v b3sum)"
```
