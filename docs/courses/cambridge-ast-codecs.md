# Cambridge AST codecs

The Cambridge `L1.Codec`, `L2.Codec` and `L3.Codec` modules expose
`termSExp`, `typeSExp`, `termJson` and `typeJson`. Each value is a
`TotalCodec` with an encoder, an optional decoder and a Lean proof
`recovers` of decode-after-encode. The shared `AstCodec.encode_injective`
theorem gives encoder injectivity for each of these codecs.
[Cambridge course index](cambridge.md) · [Verified UTF-8 JSON bridge](cambridge-json-bytes.md) ·
[Verified UTF-8 S-expression bridge](cambridge-sexp-bytes.md)

The `term` carriers are `L1.Expr`, `L2.RawExpr` and `L3.RawExpr`. L2 and L3
keep the exact names of binders and occurrences, including empty strings,
reserved words and arbitrary Unicode. Apply the course’s existing
`RawExpr.resolve []` to obtain the locally nameless AST. L3’s `loc`
constructor represents a runtime address and retains its natural-number
payload. Configurations, stores and typing environments are outside these
codecs.

## Schema version 1

Each value has the envelope `(cambridge-ast-v1 language sort body)`.
`language` is `L1`, `L2` or `L3`. The named term and type codecs use the sorts
`term` and `type`. A body is a list beginning with a constructor tag
followed by its fields in order.
The JSON representation maps lists to arrays and atoms to strings. Integer
and location payloads use canonical decimal strings to retain their full
precision across JSON consumers. A boolean is `(bool true)` or `(bool false)`,
with a string payload in JSON.

For example, applying a lambda to a negative integer in L2 has these two
presentations.

```text
(cambridge-ast-v1 L2 term
  (apply (lambda x (type-int) (var x)) (int -3)))
```

```json
["cambridge-ast-v1", "L2", "term",
  ["apply", ["lambda", "x", ["type-int"], ["var", "x"]], ["int", "-3"]]]
```

| Constructors | Languages | Fields in schema order |
| --- | --- | --- |
| `int`, `bool`, `skip` | L1–L3 | Decimal integer, Boolean atom, or zero fields respectively |
| `binary`, `if`, `seq`, `while` | L1–L3 | Left, operator (`add` or `ge`), right. Test, then arm, else arm. Left, right. Test, body. |
| `assign`, `deref` | L1–L3 | L1/L2 use an atomic location name and, for assignment, a value term. L3 uses terms for both operands of assignment and the operand of dereference. |
| `var`, `lambda`, `apply` | L2/L3 | Name. Binder, parameter type, body. Function, argument. |
| `let`, `let-rec` | L2/L3 | Binder, type, value, body. Function binder, parameter binder, domain, codomain, function body, enclosing body. |
| `ref`, `loc`, `pair`, `fst`, `snd` | L3 | Value. Decimal address. Left, right. Pair operand for each projection. |
| `inl`, `inr`, `match-sum` | L3 | Payload and sum type for each injection. Scrutinee, left binder, left payload type, left body, right binder, right payload type, right body for a match. |
| `record`, `project` | L3 | An ordered list of `(field label term)` children. Record term and label for a projection. |
| `type-int`, `type-bool`, `type-unit` | L1–L3 | Zero fields |
| `type-arrow` | L2/L3 | Domain, codomain |
| `type-product`, `type-sum`, `type-ref` | L3 | The two types in order, or the contents type for a reference |
| `type-record` | L3 | An ordered list of `(type-field label type)` children |

Record fields are separate children, so even JSON preserves declaration
order. Decoding constructs the course AST’s dependent field indices only
after checking label uniqueness. Each decoder checks the envelope,
constructor tags, child sorts and exact arities. It rejects duplicate labels
and malformed decimal payloads. Empty records are valid.

## Resolved L2 and L3 terms

`L2.ResolvedCodec` and `L3.ResolvedCodec` expose `termSExp` and `termJson`
for their locally nameless `Expr` types. They use the distinct sort
`resolved-term` in the same version-1 envelope. The existing named and
type encodings keep their tags and fields. L1 has one term AST and uses
its existing codec.

The resolved term tags and fields agree with the table above except for
variable occurrences and binder nodes.

| Constructor | Fields in schema order |
| --- | --- |
| `bvar` | Canonical decimal de Bruijn index |
| `fvar` | Literal free name |
| `lambda` | Parameter type, body |
| `let` | Type, value, body |
| `let-rec` | Domain, codomain, function body, enclosing body |
| `match-sum` (L3) | Scrutinee, left payload type, left body, right payload type, right body |

Index zero refers to the innermost binder. The recursive function body uses
index zero for the parameter and index one for the function. The enclosing
body binds the function at zero. Each match branch binds its own payload
at zero. The value codec preserves any representable index, including a
dangling one. Scope and typing checks are separate.

L2 assignment and dereference retain their string location operands. L3
preserves ordered record fields and the distinct `loc` runtime address
constructor, even if the same decimal appears in a `bvar` node. Named and
resolved term decoders check their respective envelope sorts.

## Verification

The proofs are over proper S-expression and JSON values. The regressions
also exercise text conversion with the existing S-expression reader and
printer and Lean’s JSON reader and printer. The source byte grammar is
documented separately.
[L1/L2 concrete syntax](cambridge-concrete.md) · [L3 concrete syntax](cambridge-l3-concrete.md)

```sh
lake build --wfail +Silmaril.Courses.Cambridge.AstCodec.Examples \
  +Silmaril.Courses.Cambridge.AstCodec.ResolvedExamples
```
