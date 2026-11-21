# Finite named expansion of a Prolly representation

Import `Silmaril.Formats.Dasl.Prolly.Named.Thms`. It uses the `CanName`
judgment of the named DASL layer, not a new representation. It is independent
of the choice of finite-map operations, key order and overlap policy.

- `Stored` accounts only for correctly encoded structural Prolly blocks.
  `NodeReady` supplies a finite `CanName` witness for the exact encoding of
  every leaf key and payload and every branch separator. Full expansion
  checks even a separator that duplicates a leaf key. An object link needs
  its chosen child and shallow binding; a blob link needs its exact bytes in
  the blob lane. Inline bytes do not create blob requirements.
- `Stored.namedRoot` composes these choices with the child-block bindings,
  through the existing entry and block encodings. It gives a `FullNames`
  witness at the actual root name, whose shallow spelling is the root
  encoding, not an alternative spelling of the same value. With a binding
  reference this is a compatible full expansion; no default payload is
  synthesized. The theorem asserts existence, not a resolution algorithm.
- `RootProfile.NamedRoots` considers the semantic lookup function and the
  fixed canonical builder, codec and naming profile. `namedRoot_of_stored`
  supplies existence under successful bottom-up naming, a binding reference
  containing the structural blocks, and `NodeReady`. Requiring both binding
  and structural storage rules out an expansion through unrelated child
  blocks at the selected addresses. `namedRoots_mono` preserves positive
  witnesses in binding extensions. `namedRootNames_singleton` counts root names for that
  profile given a witness. This does not identify maps with equal resolved
  payloads or force root names to agree across profiles.
- Safe raw publication writes only structural bytes. Its readback witnesses
  are for those blocks; use a decoded reference with the required object and
  blob observations to establish `NodeReady`. Neither codec success nor a
  binding snapshot by itself establishes these hypotheses. This does not
  change the byte publication or query semantics.

`lake build --wfail +Silmaril.Formats.Dasl.Prolly.Named.Examples` checks a
branch with separately bound object and blob keys sharing a carrier name,
and a snapshot where structural storage still holds but a blob target has no
finite expansion witness.
