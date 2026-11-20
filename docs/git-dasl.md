# Git objects over DASL

The [Git model](../Silmaril/Formats/Git/Defs.lean) separates a finite editable
filesystem from an indexed object graph. `Tree` stores file modes on file nodes;
`Indexed` puts these modes in the type and is equivalent to `Tree` after packing
the index. Neither admits external edges. `Path` is a list of validated
components (the empty path means the root). Raw directory constructors admit
unchecked names; the Git renderer checks every local directory. The component
check is structural, not a pathspec, a Git `fsck` check, or a checkout-safety
policy for a host filesystem.

`Object Key Ref Meta kind` keeps modes on tree edges, not on blobs. Regular
files, executables and symlinks target blobs; directories target trees;
gitlinks target commits. An opaque reference remains an opaque name even when
the object is missing. In particular a submodule need not be present in the
local store. `Expanded` excludes opaque edges by using `Empty` for references.
These are finite unfoldings, not an assertion that an arbitrary store is finite,
acyclic or collision-free. An expanded and an opaque edge can name the same
target. `treeEntries?` and `commitParts?` project one layer independently of the
representation chosen for its children.

## Layouts and recovery

Each directory occupies an object block. A file payload occupies a raw blob
block, including symlink targets. The directory entry is exactly
`{"mode": i64, "link": link}`. The mode is the integer value of the usual octal
Git spelling (`040000`, `100644`, `100755`, `120000`, `160000`). The mode
determines the required DASL link kind. A DASL object link by itself cannot tell
a tree from a commit; that distinction comes from the edge or commit field.

| Directory layout | Keys | Root representation |
| --- | --- | --- |
| `stringList` | Lean strings | Sorted `[[name, {mode, link}], ...]` |
| `byteList`, `utf8List` | Byte strings | Same arrays of pairs, sorted by unsigned byte order |
| `dict` | Lean strings | Dictionary from name to `{mode, link}` |
| `stringProlly`, `byteProlly`, `utf8Prolly` | Ordered text or bytes | Prolly leaf/branch blocks with the supplied cut policy |

The `utf8*` adapters encode each Lean string exactly as UTF-8 and sort by the
resulting bytes. Raw byte layouts do not require a valid UTF-8 sequence. Lifting
raw names to string components requires both exact UTF-8 decoding and a valid
component. List and dict codecs recover their shallow directories; the Prolly
layout provides the shared DASL `Stored` witness and root-name equality. Prolly
lookup uses the upstream read/check theorem with its store-binding and reader
soundness assumptions. Byte-key list order here is **not** the record order of
the native Git tree format.

Commit blocks use `[tree, [parents...], metadata]`. The generic codec accepts
separate codecs for the tree, parents and metadata. The name-only profile uses
object links for both tree and ordered parents. The provided metadata example is
`[messageBytes, signedTimestamp]`, without Git author/committer headers, time
zones or signatures. This is a project-local DASL layout, not native Git
serialization or a claim of wire compatibility with another implementation.

The encoder takes separate object and blob naming functions. `Rendered.store`
is a relation containing observations, not a collision-rejecting implementation
of a store. Under the **same** layout and naming functions, `renderObject_toObject`
equates the entire optional result (root and observed store) with direct
filesystem rendering, including failures. `names_toObject` states the equality
on the induced naming relation. These results do not require a hash to be
injective.

## Checks

```sh
lake build --wfail +Silmaril.Formats.Git.Dasl.Layouts.Thms
lake env lean -DwarningAsError=true --run tests/formats/GitDasl.lean
```

The regression also prints the transitive axiom dependencies of the public
roundtrips, Prolly storage witness, and object-embedding coherence theorems.
