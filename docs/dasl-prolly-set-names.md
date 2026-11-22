# Prolly-backed finite assumption sets

`Prolly.closedMap` exposes the complete result of the existing bounded block
scan, after checking that the global key order is strict. `lookup` projects
from that result and keeps the same missing, invalid and fuel behavior.
`closedSet` specializes to unit-valued leaves, and `setNames` relates each
successful root to its finite key set. The executable view is not an empty
set on failure. In particular a missing child cannot yield a partial set or
an absence verdict.

`setNames_binding` uses deterministic readback; `setNames_sound` identifies
the result with the finite set of a canonical build given `Stored`, reference
store binding, and sound reads. It does not assume unique names or claim
that every fuel bound or partial store suffices. A valid view need not have
the chunking of a specific build unless that reference is supplied.

`HOL.hypothesisKey` serializes the repository's existing canonical HOL Light
term grammar into unsigned bytewise lexicographic keys. Its inverse is the
existing HOL term parser. Keys do not name objects, and decoding keys does
not assert Boolean typing or derivability. For the logic name adapters in
`docs/dasl-logic-syntax.md`, after that stack is available, compose
`Lift.codedSet (Prolly.setNames codec read width fuel) HOL.hypothesisKey`
and pass the resulting root relation to `HOL.derivesWith` or `HOL.entailsWith`.
Use `codec := Prolly.setCodec Prolly.byteKey`. This is an assumption set, not a
replacement for the ordered HOL bound-variable typing context.

```sh
lake build --wfail +Silmaril.Formats.Dasl.Prolly.Set.Thms \
  +Silmaril.ProofFormats.DaslSyntax.HOL.Prolly.Defs
lake env lean -DwarningAsError=true --run tests/formats/DaslProllySet.lean
```
