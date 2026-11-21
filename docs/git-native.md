# Native Git loose-object preimages

The [native encoder](../Silmaril/Formats/Git/Native/Defs.lean) is a second
interpretation of the [same kind-indexed objects](git-dasl.md). It emits the
uncompressed hash preimage (`kind`, a space, the decimal payload byte count,
NUL, payload), not the zlib-compressed loose file. It does not cover packs,
tags, legacy noncanonical modes, Git checkout policy, or full commit parsing.
See Git's [loose-object specification](https://git-scm.com/docs/gitformat-loose)
and [`base_name_compare`](https://github.com/git/git/blob/v2.52.0/tree.c#L101)
for the format and tree comparator.

- Blobs use their exact bytes. Tree records use `mode SP basename NUL raw_oid`.
  The canonical mode spellings are `40000`, `100644`, `100755`, `120000`, and
  `160000`. Tree order uses unsigned basename bytes with a virtual slash only
  for directories; for example `foo.`, directory `foo`, then `foo0`. Symlinks
  and gitlinks have no virtual slash. Native names need not be UTF-8. The
  structural check rejects empty, `.` or `..` components and NUL or slash.
- Commits use exactly one `tree` line, zero or more ordered `parent` lines,
  then one each `author` and `committer`, then a blank line and the exact
  UTF-8 message without NUL. Headers use LF; the encoder does not alter the
  message or append a final newline. Identity fields use printable ASCII:
  nonempty display names without leading/trailing spaces, nonempty email
  tokens without spaces, and neither field may contain angle brackets.
  Timestamps are decimal nonnegative seconds below `2^63`, with fixed `+0000`.
  There are no extra headers, signatures, alternate encodings, or tag objects.
- A profile supplies a reversible key encoding, an exact-width name byte
  codec (20 bytes for SHA-1, 32 for SHA-256), and a choice of child names for
  encoded child preimages. Commit IDs in headers use lowercase hex. Opaque
  references, including gitlinks, are emitted without claiming availability.
  The abstract `names` relation applies the supplied naming relation to
  resolved objects; `Profile.Compatible` states the assumption for the child
  name choice. No hash injectivity, collision freedom or store closure is
  assumed.

`renderObject_toObject` and `names_toObject` prove that embedding the simple
filesystem into the full object syntax preserves both native bytes (including
failure) and the induced naming relation under the same profile. The analogous
DASL theorems are in [the DASL model](git-dasl.md).

See [native-to-DASL name correspondence](git-translation.md) for the combined
bottom-up interpretation and its audit boundary.

`tests/formats/GitNative.lean` compares output byte-for-byte against preimages
from Git 2.47.3 `mktree --missing -z` and `commit-tree`, in SHA-1 and SHA-256
repositories. The fixtures include prefix-sensitive tree ordering, a non-UTF-8
basename, a symlink, a subtree, a gitlink and a two-parent recursive commit.

```sh
lake build --wfail +Silmaril.Formats.Git.Native.Thms
lake env lean -DwarningAsError=true --run tests/formats/GitNative.lean
```
