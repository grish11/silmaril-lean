# Typed DASL encodings and measurements

This layer uses the [abstract DASL model](atproto-dasl.md), not Lexicon and not
a second wire codec.

## Encodings

- [Encode](../Silmaril/Formats/Dasl/Encode/Thms.lean) exposes first-class
  `TotalCodec` and `PartialCodec` values. Both recover a source on every
  successful encoding. This is a left inverse, not a claim that every
  accepted input is canonical. `DefaultCodec` is an opt-in total default;
  callers can choose a different representation. `UInt64` encodes the bit
  pattern, and `Int64` uses the same constructor through `toUInt64`/`toInt64`.
  There are separate codecs for inline bytes, typed shallow links, and fully
  resolved blobs. Typed dictionaries keep the finite field set, and typed
  lists preserve order and length.
- [OrderedMap](../Silmaril/Semantics/OrderedMap/Thms.lean) validates strictly
  ascending keys, identifies lookup with entry membership, and proves equality
  from pointwise lookup. [Map codecs](../Silmaril/Formats/Dasl/Encode/Map/Thms.lean)
  encode lists of pairs `[k,v]` or lists of exact `{"k":k,"v":v}` records.
  An empty map has the same representation in both layouts; nonempty entry
  shapes differ. Decoding checks the order of *decoded* keys, so duplicates
  are rejected even if a permissive key decoder accepts more than one spelling.
  Encoder recovery prevents two distinct source keys from encoding to the same
  key. Sets use the same order and duplicate check without dummy wire values.
- `codedNames` relates a name to a value only through that codec's emitted
  representation; a decoder accepting alternative spellings does not add names
  to this relation. Binding of the raw relation transfers by recovery. For at
  most one name per source, separately assume raw `UniqueNames`, or a fixed
  hash graph and deterministic serialization defined on emitted representations.
  No hash injectivity is needed. For bottom-up roots this only applies if the
  encoder already fixes all child names included in the root representation.
  For semantic quotients with several representations, raw `UniqueNames` does
  not imply one root name per equivalence class.

## Metrics

[Measure](../Silmaril/Formats/Dasl/Measure/Thms.lean) counts AST constructors
and link constructors, and measures their maximum counts along a path. Inline
metrics stop at links; unfolded metrics count repeated occurrences. A blob
is one link constructor with a raw payload, not an inline child. `blocks`
counts the root and all expanded target occurrences. Unresolved links count
toward link metrics but contribute no observed target blocks. A partial tree
therefore measures observations, not the unobserved portion of the store.

Distinct footprints count typed object/blob names instead of occurrences.
Membership of an observed block implies the corresponding naming witness,
and under binding equal typed names yield equal blocks. Per-block maximum
shape/byte measurements bound every observed block. Byte measurements take an
explicit object serializer; raw blobs use their actual byte length. A failed
serialization does not contribute zero. The distinct-byte reader must satisfy
`byteSizeAgrees`; a specification reader follows from binding lookup. None of
these definitions imply a compression, hash, Prolly distribution, or size limit.

```sh
lake build --wfail +Silmaril.Formats.Dasl.Encode.Map.Thms +Silmaril.Formats.Dasl.Measure.Thms
lake env lean -DwarningAsError=true --run tests/formats/Dasl.lean
```
