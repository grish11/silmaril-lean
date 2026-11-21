# Arena codec views

`Silmaril.Formats.Dasl.Arena.{Defs,Thms}` lifts the existing partial codecs over
the arena from `Silmaril.Semantics.Arena`. Use `Codec.lift` for a name-independent
codec, or supply a codec indexed by the slot's **existing** `Option Name`. The
selected codec receives `none` for anonymous residents; it cannot assign a name.
`Codec.then` composes typed-to-shallow and shallow-to-byte codecs using the same
name in both stages. With a `TotalCodec`, pass `.partial` to use the same API.
For stage-qualified diagnostics, run each stage separately; composition coalesces
stage failures to rejection. The CBOR adapter is the already checked
`Wire.canonicalCodec`, not a separate serializer or an assumed total encoding.

- Strict single-cell conversion distinguishes success on a hole (`ok none`), a
  nonresident slot (`ok (some slot)`), and a failing resident (`error ()`). A
  strict dense conversion scans in ascending index order and returns the first
  rejecting index, not a partially converted arena. A sparse generic-key state
  can be checked pointwise without requiring a finite enumeration of its keys.
- Discard conversion preserves occupancy and the exact optional name, dropping
  only rejected local payloads. Use `Converter.rejected` on the input to observe
  the loss. A discarded resident is not a statement of absence in a CAS.
- `Codec.decode_encode_discard` recovers the original state on successful
  encodings. There is no converse law for arbitrary decoder-accepted inputs.
  Successful encoding gives evidence of provenance (`Codec.image`) but no hash
  or publish authorization: `Codec.encode_discard_admitted` requires inclusion
  of that image in the destination reference. Binding of an image follows from
  binding at the source and determinism at each name, not hash injectivity.
  `raw_discard_observations` relates the name-independent parser to the existing
  raw-store object lane, with the object name guard retained. Raw blob witnesses
  are unchanged by the existing raw-store interpretation, not parsed as objects.
- `Dense.equivPacked` gives the fixed-length `Array Slot` alternative exactly
  when all in-bounds cells are occupied. An anonymous slot with no payload is
  still a slot. Clearing can leave this subtype, so use the optional-slot
  representation for unrestricted raw edits.

The fixtures are checked with `lake build --wfail +Silmaril.Formats.Dasl.Arena.Examples`.
Dependency completeness and cache evidence are separate from representation
conversion. Discard conversion is not the appropriate source for verified
negative queries.
