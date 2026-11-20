# Named DASL: observation and lifting

`Silmaril.Formats.Dasl.Named.Thms` works on the landed `Named Name` (`Tree Empty
Name`), not a second AST. Resolved object edges carry a name and child tree;
resolved blobs carry a name and the original bytes. Inline bytes are not blob
edges. `Named.erase` is the existing projection to abstract `Value`.

- `Named.observed` is `tree.embed.bindings`. It is the least relation admitting
  the witnesses present in the tree. An object witness is the **shallow** target
  (including the names of its outgoing links); a blob witness is its exact bytes.
- `AdmittedBy` is inclusion into an arbitrary relation. `Compatible` additionally
  requires the supplied store to be binding. `Coherent` asks for binding only
  on the observation itself, equivalently existence of some compatible store.
  `Conflict` gives an explicit same-name/unequal-target witness and excludes
  every binding extension. Aliases naming the same target are not conflicts.
  The object and blob lanes are separate; a profile may additionally require
  disjoint name domains. These checks do not establish hash integrity.
- `Named.Valid store` is a proof-carrying subtype, not a change to the core
  syntax. `admitted_iff_expands` relates the witness check to the existing finite
  `Expands` judgment at the tree's own shallow projection. It does not add a
  store binding for the inline root; use `FullNames` for a separately named root.
- `CanName store value source` makes the bottom-up naming choices explicit.
  The parent object pair must be admitted at the shallow target that those
  choices *actually* construct. Every list index and dict key is checked. A
  nameless value has a compatible lift iff the store is binding and such choices
  exist. Binding does not imply existence. In the fresh-name fixture an
  injective supply of names suffices for a flat list of arbitrary blob bytes
  when the store can be chosen; it says nothing about a fixed CAS or digest.

For a raw store, instantiate the result with `RawStore.Decoder.view`: an object
choice then requires an eligible name and original bytes that actually parse to
the chosen shallow target. A blob choice requires an eligible raw name and the
exact bytes. A writer must establish the applicable `render?` success and
parse-back law on each chosen shallow target, plus the caller's raw binding and
integrity policy. The lifting theorem itself performs no encoding or hashing.

`lake build --wfail +Silmaril.Formats.Dasl.Named.Examples` checks the nested
object/blob lift, incoherent object witnesses, fresh blob names, and a decoded
raw store accepting a valid binding and rejecting an unparseable one.
