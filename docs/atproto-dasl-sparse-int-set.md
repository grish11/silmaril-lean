# Sparse signed integer sets

The [layout](../Silmaril/Formats/Dasl/SparseIntSet/Defs.lean) stores distinct `Int64`
keys in ascending signed order. It uses the ordered-set codec from the
[DASL encoding API](atproto-dasl-encodings.md): the shallow object is a single
array, with one signed i64 per member and no child blocks. The reader rejects
duplicates, descending keys, and non-integers. `normalize` is the separate
constructor for arbitrary lists; it sorts and deduplicates.

The [theorems](../Silmaril/Formats/Dasl/SparseIntSet/Thms.lean) give an equivalence
between the **normalized** layout and `Finset Int64`. Two input lists normalize
to the same layout exactly when they have the same members. Membership checks
the stored keys with a list scan. Cardinality is the key count and equals the
finite set's cardinality. The object block count is one, block depth is zero
when counting child-link hops, and a successful encoding's byte size is its
`ByteArray.size`. This is not a compression or runtime-performance result.

## Wire and names

The [profile adapter](../Silmaril/Formats/Dasl/Wire/Profile/Defs.lean) combines the
layout codec with the existing signed-i64 DRISL writer and reader. It returns
bytes only when decoding them recovers the source. It does not assume all
abstract names or trees serialize. The test exercises both profiles against the
same link-free golden bytes and separately checks BDASL tag-42 links with
BLAKE3 CIDs, rejecting unsupported codecs and object/blob mismatches. A raw
CID cannot be used to read a set root. See `dasl-cid`, `drisl`, and `bdasl` in
[references.bib](../references.bib), in particular BDASL § Parsing BDASL CIDs.

The [naming theorems](../Silmaril/Formats/Dasl/Wire/Profile/Thms.lean) only count
roots for the chosen encoder's output. `canonical_root` needs successful
serialization, a fixed addressing function with which the store agrees, an
object-eligible result, and a store entry at that name. No injectivity of the
hash is assumed: store binding is a separate hypothesis for binding roots, not
a proof of unique names. Wire profile, addressing function, and digest
verification stay separate. The test fixtures check CID syntax, not digest
integrity, and this slice implements neither hashing nor streaming verification.

```sh
lake build --wfail +Silmaril.Formats.Dasl.SparseIntSet.Thms +Silmaril.Formats.Dasl.Wire.Profile.Thms
lake env lean -DwarningAsError=true --run tests/formats/DaslSparseIntSet.lean
```
