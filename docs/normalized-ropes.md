# Normalized concatenation ropes

The [generic tree](../Silmaril/Semantics/Rope/Defs.lean) can hold arbitrary lists,
with adapters for raw `ByteArray` and exact Lean `String`. Raw concatenation adds
a binary node without copying its payload into a new leaf. Its shape need not
be canonical: the observation is the flattened sequence. Text sizes count Lean
`Char` values, not UTF-8 bytes or grapheme clusters; use the byte adapter for
raw UTF-8 storage.

For a fixed geometry, normalization flattens and rebuilds the tree. It splits
payload into full positive-size pages and at most one short trailing page. It
groups each successive tree layer into branches with a power-of-two fanout
limit: binary at exponent zero, four-way at exponent one, and so on. The bias
chooses which end receives the partial group, without reversing leaf order.
One-child branches within a layer preserve common leaf depth.

The [theorems](../Silmaril/Semantics/Rope/Thms.lean) prove flatten recovery,
concatenation semantics, extensional canonicality at fixed geometry,
idempotence, normal-form equivalence with lists, exact leaf lengths and element
count, nonempty bounded branch fanout, and uniform leaf levels. The adapters
recover original bytes and strings. The implementation reports structural
depth, but does not claim logarithmic edits or measured performance. This is an
in-memory rope, not a DASL wire format or an IPFS/Unison implementation.

```sh
lake build --wfail +Silmaril.Semantics.Rope.Thms
lake env lean -DwarningAsError=true --run tests/semantics/Rope.lean
```
