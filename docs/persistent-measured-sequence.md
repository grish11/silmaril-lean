# A persistent measured sequence

`MeasuredSequence` models persistent edits with a cached element count at each
join. It is inspired by the use of element measures in Unison's sequence
structures, not a model of the Unison runtime or its finger-tree digits.
This complements paged ropes: the unit here is a generic element, and the
focus is the behavior of path-local edits before an explicit rebuild.

`append`, indexed lookup and replacement, `splitAt`, and `splice` implement
ordinary list behavior. Splitting at a join boundary returns both original
children; replacement rebuilds only the path it takes. Splits clip at the end,
replacement outside the sequence has no effect, and splicing past the end
appends the inserted sequence. The operations preserve the validity invariant
(exact cached sizes and no empty children at a join), when their inputs are
valid. No claim about runtime allocation or automatic rebalancing is made.

`normalize` rebuilds from elements by a deterministic midpoint bisection. It
preserves the list and returns a valid tree whose left child at each join has
the floor half of the elements. It is idempotent, and two trees normalize to the
same tree exactly when their lists agree. `normalEquiv` relates only the
normalized subtype to lists, not the raw editable shapes.

## DASL layouts

Both layouts take a caller-supplied recoverable element codec. The editable
layout uses null for empty, a singleton array for an element, and a pair for a
join. It recovers the exact inline tree for valid inputs. A subtree position
may instead contain an object link to a valid tree supplied by a resolver;
blob links, unresolved object links, and empty join children are rejected.
Leaf payloads are interpreted only by the element codec. Cached sizes are not
serialized: decoding derives them from the recovered children. The resolver
supplies already decoded trees; this is not a recursive block-store reader.

The separate normalized layout encodes only the ordered array of elements and
decodes to the midpoint rebuild. Encodings agree exactly when the elements
agree, regardless of the original join shape. Every accepted normalized
representation re-encodes exactly if the element codec has no decode aliases.
`normalizeShape?` also works from any successfully resolved editable shape.
The layouts do not choose names or compute hashes. Concrete serialization is
partial and uses the selected wire profile, including its link-kind checks.

```sh
lake build --wfail Silmaril.Formats.Dasl.MeasuredSequence.Thms Silmaril.Formats.Dasl.Wire.Defs
lake env lean -DwarningAsError=true --run tests/semantics/MeasuredSequence.lean
lake env lean -DwarningAsError=true --run tests/formats/DaslMeasuredSequence.lean
```
