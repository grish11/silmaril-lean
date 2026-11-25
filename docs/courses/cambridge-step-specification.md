# Cambridge step specifications

A step specification is a finite conjunction of positive one-step claims
in L1, L2 or L3. Each endpoint is a bounded reference into a catalogue of
complete course configurations, including the expression and store. The
caller supplies the catalogue. The language selects the existing
operational adapter. In L2 this is call by value. In L3 distinct fresh
locations give distinct permitted edges.
[Operational adapters](../projects/operational-institutions.md#cambridge-l1-and-l2)

## Context and satisfaction

A context fixes the language and a slot count `n`. Each name has Lean
type `Fin n`. A signature morphism maps slots within the same language.
The sentences use the repository's conjunction fragment over
unit-labelled steps. The empty conjunction is true. Each clause asserts that an edge is
allowed. A conjunction can name different alternatives from the same
source, as in the L3 allocation example.

A catalogue is a function from the context's slots to the selected
language's actual `Config` type. It induces an operational signature map.
`translation` maps both endpoints of each claim to full configurations
and pulls the target edge relation back to the slots. The resulting
institution corridor preserves and reflects satisfaction. For the
registered models, `holds_iff` identifies truth with the course's direct
`Step` predicate at every edge.
[Lean institution and translation](../../Silmaril/Courses/Cambridge/StepSpecification/Institution.lean)

## Canonical JSON

For a catalogue of three L1 configurations, the following document
asserts one step from slot zero to slot one.

```json
["cambridge-step-spec-v1", "L1", "3", ["all", ["step", "0", "1"]]]
```

The L1 regression uses this catalogue.

| Slot | Expression | Store |
| --- | --- | --- |
| 0 | Assign 42 to `x` | `x ↦ 7` |
| 1 | `skip` | `x ↦ 42` |
| 2 | `skip` | `x ↦ 7` |

The displayed document is true in that catalogue. Changing the target to
slot 2 gives a well-formed false specification. Slot 3 is out of range
and makes the document malformed.

The header carries the language and slot count. Each clause has a
`step` tag and two canonical nonnegative decimal strings. The decoder
checks the header against the expected context and checks each reference
against the slot bound. Clause order is preserved by the codec.
The catalogue is supplied separately from the document. These sentences
have their own envelope. The program AST codecs represent expressions
and types.
[Program AST schemas](cambridge-ast-codecs.md)

`json` is a `TotalCodec` over structured `Lean.Json` values. Its
round-trip theorem establishes recovery of the typed sentence from its
encoded value. `meaning` returns `none` when decoding fails and
`some P` for a well-formed document, where `P` is the proposition that
the registered course model satisfies the sentence. A decoded sentence
can be false. The API leaves satisfaction as a proposition.

`jsonBytes` composes the same schema with the verified RFC 8259 UTF-8
reader and printer. Its separate round-trip theorem recovers a typed
sentence from its emitted bytes. `meaningBytes` applies the same semantic
interpretation after byte decoding. External JSON documents can use
whitespace and alternate string escapes. Re-encoding selects the
canonical spelling.
[Verified UTF-8 JSON bridge](cambridge-json-bytes.md)

## Checked examples

The L1 catalogue distinguishes a successful assignment from an edge to
the same expression with the old store. The L2 catalogue checks both
call-by-value steps and rejects a direct edge that skips argument
evaluation. The L3 catalogue supports two different fresh allocations
and rules out allocation at an occupied location. Malformed examples
exercise wrong language and count, out-of-range references, noncanonical
integers and program documents.
[Lean examples](../../Silmaril/Courses/Cambridge/StepSpecification/Examples.lean)

```sh
lake build --wfail +Silmaril.Courses.Cambridge.StepSpecification.Examples
```

Finite may-return claims have a separate versioned specification format.
The step tree codec also composes with the verified UTF-8 S-expression
bridge.
[May-return specifications](cambridge-return-specification.md) · [S-expression text](cambridge-sexp-bytes.md)
