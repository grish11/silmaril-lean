# Cambridge finite may-return specifications

L1, L2 and L3 return documents use the same typed configuration catalogues
as step documents. A catalogue slot names a full course configuration,
including the expression and store. The return institution reads the
registered adapters' `OpSem.May` observations.
[Step specifications and catalogues](cambridge-step-specification.md) ·
[Operational adapters](../projects/operational-institutions.md#cambridge-l1-and-l2)

## Sentences and satisfaction

A sentence is a conjunction of claims. Each claim names a source slot.

- `may-return` asserts that some finite run from the source returns a
  value. The witness can be any full configuration of that language.
  The catalogue need only name the source.
- `may-return-to` names a destination slot as well. It asserts a finite
  run returning exactly that configuration, including its store.

A run can use zero steps when its starting expression is already a value.
The claims are existential and conjunctions can describe several possible
alternatives from the same source. The empty conjunction is true.

The catalogue translates the source and any named destination to actual
configurations, and the model reduct pulls back the resulting observation
predicate. `satisfaction` gives both directions across this translation.
`may_return_iff` and `holds_iff` identify those observations with the direct
course step closures ending in values.
[Lean institution](../../Silmaril/Courses/Cambridge/ReturnSpecification/Institution.lean)

## JSON and structural S-expressions

The return format uses the envelope `cambridge-may-return-spec-v1`.
The language and slot count select the same typed context as for step
documents. Slot references are canonical decimal strings within that
count. Existing `cambridge-step-spec-v1` documents keep their schema and
decoder.

```json
["cambridge-may-return-spec-v1", "L3", "3",
 ["all", ["may-return", "0"], ["may-return-to", "0", "1"]]]
```

The corresponding proper S-expression value has this shape.

```text
(cambridge-may-return-spec-v1 L3 3
  (all (may-return 0) (may-return-to 0 1)))
```

`json` and `sexp` are codecs over structured JSON and proper
S-expression values. `jsonBytes` adds the verified RFC 8259 UTF-8
reader and canonical printer. Each codec proves decode-after-encode
at its own representation type.

`jsonToSExp` and `sexpToJson` check an input against the context and
translate through its typed sentence. Both directions preserve the
optional satisfaction proposition, including failure on malformed
input. A well-formed false sentence still has a proposition. These
APIs leave proof of that proposition to Lean.
[Lean codecs](../../Silmaril/Courses/Cambridge/ReturnSpecification/Format.lean) ·
[UTF-8 JSON bridge](cambridge-json-bytes.md)

## Checked examples

The examples verify an L1 store update and a zero-step return, and
the two-step call-by-value return in L2. In L3, dereferencing a fresh
allocation can return the integer 42 with different stores. Allocation
at location 1 and allocation at location 2 give distinct witnesses
for the same existential sentence with only its source in the catalogue.
A second sentence names both possible final configurations.

```sh
lake build --wfail +Silmaril.Courses.Cambridge.ReturnSpecification.Examples
```

Must returns, divergence and other logics remain separate.
The structural S-expression codec also composes with the verified
canonical UTF-8 bridge.
[S-expression text](cambridge-sexp-bytes.md)
