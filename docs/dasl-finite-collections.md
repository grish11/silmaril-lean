# Finite DASL collections

Use `Encode.finiteSet` for a finite set (`Finset α`) and `Encode.finiteMap`
for a finite map (`OrderedMap α β`). Both take independent codecs for keys;
maps also take a value codec and an entry layout (`pairEntry` or
`recordEntry`, for example). These are first-class codecs, not instance
coherence rules. A fixed total codec recovers its input, and equality of
emitted representations is equivalent to extensional equality of the
collections. This does not assert equality across layout choices or spellings
accepted by a decoder.

Semantic sets are `Set α`; semantic maps are partial lookups `α → Option β`.
For a total codec on the corresponding finite type, exactly the finite sets
and finitely supported lookups have a decoded representation. This is a
representation theorem, not an algorithm to decide finiteness of an arbitrary
predicate or function. `OrderedMap.ofLookupOn` tabulates on supplied finite
keys and omits `none`s; outside that universe its result is always `none`.

An association list is not the semantic map. The ordered representation is
unique by lookup; parsing validates strict order by *decoded* key equality
and order and rejects duplicates even if syntactically distinct aliases
decode to the same key. Successful encoding cannot collide on keys because
each key codec recovers its input. `OrderedMap.transportEquiv` transports
keys and values along equivalences, re-sorting in the destination key order.

`Encode.TotalCodec.viaEquiv` (and the partial counterpart) adapts existing
layouts without changing their recovery contracts. For example,
`Encode.signedRangeSet` exposes the maximal signed range layout over
`Finset Int64`. Use `Wire.Profile.codec` to connect a compatible shallow
layout to DASL or BDASL bytes; rendering can still fail on profile guards.
The separate Prolly string/object index is a block layout with its own
policy, store, and closed-view lookup contract, not a new collection equality.
