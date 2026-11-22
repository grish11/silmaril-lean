# Name-ordered DASL link sets

Use [`NameLinkSet`](../Silmaril/Formats/Dasl/NameLinkSet/Defs.lean) as the
default for **new link-indexed operations**. `objectKey` and
`blobKey` use the caller's `LinearOrder` on names; `mixedKey` uses tagged names
(objects first, then blobs, each in name order). The generic `codec` accepts a
recovering key codec and checks that decoding retains the exact input links.
The shallow format is one array of links in strictly increasing key order.
Decoding needs no store. `normalize` sorts and deduplicates input keys;
decoding rejects unordered or duplicate entries rather than repairing them.

## Resolved named view

[`ResolvedView`](../Silmaril/Formats/Dasl/NameLinkSet/Resolved/Defs.lean)
attaches a fully resolved `Dasl.Named` child to each object member and raw
bytes to each blob member. It retains each top-level name and any names inside
object children. `entry` returns an ordinary named object or blob node;
`toNamed` returns a named list in reference-set order. Replacing the expanded
targets by their links recovers the exact original layout. The layout, lookup,
recovery and the resolved view's erased `contents` do not require a store.

`ResolvedView.Valid` is separate: it tests the view against a caller's naming
relation on tagged links and named nodes. `ValidIn` specializes this to the
existing `Dasl.Expands` semantics, including nested bindings. A valid view is
a full expansion of the reference array; a binding store gives at most one
such named tree. For a binding naming relation, the erased contents of a valid
view agree with the relation's content image. This view accepts supplied
targets; it is not a recursive resolver or a new AST. Shallow wire reads still
do not establish nested validity.

## Two views of name order

`SortedNamed` takes the other route: its value is the ordinary resolved named
AST, with a structural proof that its shallow projection is exactly a sorted
array of the chosen links. It does not store a second key array. `ofView`
materializes a `ResolvedView` as this subtype, and `forget` recovers the exact
original layout through the existing reference codec. The separate `ValidIn`
predicate checks the full expansion against a store.

| Interface | Simpler lookup or recovery law | Tradeoff |
| --- | --- | --- |
| `Layout` plus `Index` and a reader | `lookup_eq_some_iff`: a member gets exactly its callback result. `recovers` is a wire-layout round trip without a store. | Keeps binary search and distinguishes unresolved, missing and invalid targets. A positive read needs a sound reader to say anything about the store. |
| `SortedNamed` | `lookup_matches`: a hit is a resident AST child with that exact typed link. `lookup_none_iff` agrees with the forgotten reference set. | No callback or store access for lookup; the simple implementation scans the top-level children. Full store soundness is a separate `lookup_sound` theorem. |

For a binding store, `SortedNamed.compatibleEquiv` identifies exactly the
reference layouts **admitting a full expansion** with the store-valid sorted
named trees. `ofExpansion` accepts supplied expansion evidence; the inverse
to `forget` in the equivalence chooses from the existence proof. Binding
gives uniqueness, not existence. Missing, invalid or unexpanded descendants
can keep a structurally valid reference layout outside this equivalence. This
is not an additional codec or an executable resolver.

## Wire profiles and indexing

For DASL or BDASL, select `cidOrder` explicitly for unsigned lexicographic CID
bytes, and use `cidWireCodec` with the corresponding wire profile. It checks
the CID codec kind (`0x71` object, `0x55` raw blob) on write and read. A mixed
layout can distinguish two tags on the same abstract name only when its profile
permits it; the concrete CID guards are disjoint. Wire representation remains
partial and neither profile here verifies a digest or assumes that every
abstract name serializes. The order and key codec must be part of the agreed
layout, not inferred from the bytes.

`index` builds a sorted array once. Its binary search is proved equivalent to
name membership; each failed pivot discards a side and narrows the window to at
most half its width. This does not bound the cost of key comparison, decoding,
index construction, or block reads. `lookup` returns `none` for an unindexed
name. An indexed name can be unresolved (caller did not obtain a result),
missing (no bytes observed), invalid (wrong kind or ill-formed object), or
found. Blob bytes are not parsed as objects. Negative outcomes do not show
semantic absence. Positive wire reads are sound for every store relation that
contains the observed byte bindings; a binding store then gives a unique
decoded payload **per tagged name**.

The [theorems](../Silmaril/Formats/Dasl/NameLinkSet/Thms.lean) characterize
layouts as finite sets of keys and prove recovery, kind admission, exact link
identity and lookup soundness. `contents` is the relational image of the
members; multiple member names may resolve to the same payload. Name
cardinality does not count distinct contents. `ofContents` takes a caller's
total name selector, required to bind the requested values when interpreting
the result. Under that coherence and a binding relation the content view
recovers the input set, and layouts are canonical for that fixed selector and
order. This does not prove wire-encoding existence or choose a representative
for aliases. Two coherent selectors can produce different bytes for the same
content, even under one binding relation.

## Choosing a collection API

The [DASL and BDASL comparison fixture](../tests/formats/DaslNameLinkSet.lean)
uses the same object value (`7`) in three ways:

| Use case | API | What it retains |
| --- | --- | --- |
| Test whether `7` is present, with no external references. | `SparseIntSet.codec` (built with `Encode.setOf`) and `SparseIntSet.contains` | Just the inline values. No reader or naming policy. |
| Store payloads out of line, deduplicating repeated `7` alongside a raw blob. | Existing [`LinkedSet.normalize?`](atproto-dasl-linked-set.md) | One entry per content value, using the profile's preferred links. |
| Address two different names that both resolve to `7`. | `NameLinkSet.normalize` and `Index` | Each typed name remains independently addressable. The alternate alone round-trips in the name codec but the content codec rejects it as nonpreferred. |

The optional [compatibility module](../Silmaril/Formats/Dasl/NameLinkSet/Compatibility/Thms.lean)
provides an explicit conversion, `ofContentLayout`. It reorders the original
typed links without resolving them or choosing new names. `reindex_contains`
matches indexed membership against entries in the old layout with no reader
assumptions. For a valid layout under a fixed content profile,
`reindex_member` says membership in the reader's content image agrees exactly
with `LinkedSet.Member`; after successful normalization it agrees with input
membership (`reindex_normalize_member`). Equality of the reindexed layouts
or even just their content images reflects equality of the original layouts
under that same profile (`reindex_eq_iff`, `reindex_contents_eq_iff`). This
does not extend to arbitrary name layouts: distinct singleton aliases can
have the same image even under a deterministic reader. Failed reads supply no
binding in that image, not proof of semantic absence in a more complete store.

The existing content and nameless APIs and their wire interpretations are
unchanged. The linked layouts can share array syntax but have different
ordering and validity rules. Choose the codec explicitly; don't use one as a
fallback parser for the other.

```sh
lake build --wfail +Silmaril.Formats.Dasl.NameLinkSet.Compatibility.Thms +Silmaril.Formats.Dasl.NameLinkSet.Resolved.Thms
lake env lean -DwarningAsError=true --run tests/formats/DaslNameLinkSet.lean
```
