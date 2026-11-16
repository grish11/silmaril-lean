# Languages in a silmaril project

A project can name **languages** — sets of byte strings, Unicode strings, numbers, trees or any
other domain — say how each was built, and ask the standard questions about them as ordinary
project problems. Everything below is Lean: the registry generates or checks each language's
definition, and every claim about a language is a problem with answers (proofs) or none.

| Piece | Where |
| --- | --- |
| Constructors (`formatLang`, `artifactLang`, `within`) | `Silmaril.Project.Languages.Defs` |
| Record kinds `language_domain`, `measure`, `language_interpretation`, `language` | `Silmaril.Project.Registry.Language.Defs` |
| Standard shapes `silmaril.shapes.language.*`, built-in domains and measures | `Silmaril.Project.Shapes.Language.Defs`, readings in `….Thms` |
| Wasm interpretations | `Silmaril.Project.Languages.Wasm.Defs` |
| Regular expressions over any monoid | `Silmaril.Semantics.Accept.MonoidRegex` ([accept-regex.md](../accept-regex.md)) |
| Worked fixtures (the self-test) | `examples/project/ProjectSelfTest/Languages.lean` |
| Database tables | `tools/silmaril-project/src/project/schema/languages.rs` |

## Domains, measures, interpretations

```lean
silmaril language_domain bytes := Silmaril.Project.Languages.Bytes      -- List UInt8
silmaril measure bytes.length := Silmaril.Project.Languages.bytesLength (domain := bytes)
silmaril language_interpretation wasm.core.accept_bytes32 :=
  Silmaril.Project.Languages.Wasm.acceptBytes32 (domain := bytes)
  (abi := Silmaril.Wasm.Game.Accept.Callout.bytes32) (environment := Silmaril.Wasm.Game.UEnvOk)
```

A **domain** is a Lean type, its carrier. Lean records whether it has a `Monoid` instance and,
for `List α`, the letter type `α`. Built in: `bytes` (`List UInt8`), `unicode` (`List Char`,
strings of Unicode scalar values), `nat` (`ℕ`), `nat.additive` (`Multiplicative ℕ`, the
monoid `(ℕ, +)`), `nat.lists` (`List ℕ`). A project adds its own (the self-test registers
JSON trees and JSON event streams).

A **measure** is a function from a domain's carrier, into any type; the bound shapes and
`within` need it into `ℕ`. Built in: `bytes.length`, `unicode.length`,
`unicode.utf8_length`, `nat.value`, `nat.lists.length`; the self-test adds JSON tree depth.

An **interpretation** `I : V → Set T` says how a value of type `V` (a decoded artifact) denotes
a language. Its `abi` and `environment`, when given, must occur in `I`'s definition, so they
name the definitions the semantics actually uses, not labels.

## Languages

`silmaril language N (domain := D) (op := …) …` (or a `[[language]]` table). Except for
`op := decl`, Lean generates the definition `N`, so the language *is* its construction:

| `op` | fields | definition |
| --- | --- | --- |
| `decl` | `decl := L` | an existing `L : Set T` |
| `format` | `format := F` | the byte strings the project format `F` parses |
| `artifact` | `value := X`, `interpretation := I` | `I` of the value the CID-pinned bytes of `X` parse to |
| `union`, `inter`, `diff` | `args := [A, B, …]` | `∪`, `∩`, `\` |
| `regex` | `decl := e`, `args := [leaves…]` | `Regex.Expr.eval` over `List α`, `MonoidRegex.Expr.eval` over a monoid |
| `within` | `args := [A]`, `measure`, `bound` | `{x ∈ A ∣ μ x ≤ b}` |

Ill-typed combinations are errors, in Lean and again in `sil project check`: operands,
interpretations and measures must be over the language's domain, a format language is over
bytes, and a regular expression needs a list domain or a monoid.

**Identity.** Each language has an `identity`: a JSON description of its construction with no
display name (defining constants, the CID and format of an artifact with the
interpretation's definition, ABI and environment, operators with their operands' identities,
the carrier). `sil project` stores it with its BLAKE3 hash (`languages.identity_hash`).
Renaming a language or retitling it does not change its identity, and the artifact hash alone
is never the identity of an artifact language — the interpretation is part of it. Two
different constructions of the same set have different identities; that they are equal is a
problem (`eq_at`) to be proved.

`title`, `doc` and `source` (a `references.bib` key such as `rfc8259`) are provenance kept as
written. A wrong language is **deprecated**, not deleted: `silmaril deprecation N (reason := …)
(superseded_by := [M])` works for languages as for problems and specs.

## The standard problems

Each shape keeps the sentence `x` last; an instance that fixes everything else is a problem
over the domain, and its statuses are the questions (proved in
`Silmaril.Project.Shapes.Language.Thms`):

| shape | THM | SAT | UNS | CSA |
| --- | --- | --- | --- | --- |
| `member L x` | `L` universal | `L` nonempty | `L` empty | `L` not universal |
| `subset_at L K x` | `L ⊆ K` (refinement, directional) | | | a counterexample in `L \ K` |
| `eq_at L K x` | `L = K` | | | a counterexample |
| `bound_at L μ b x` | every member has `μ x ≤ b` | | | a member above the bound |
| `eq_within_at L K μ b x` | `L = {x ∈ K ∣ μ x ≤ b}` | | | a counterexample |
| `bytes_member L b` | (closed, with a registered value for `b`) artifact membership | | | |

Fixing `x` as well is **sentence membership**: THM true, CSA false, no answer unknown. A CSA
proof written `⟨x, h⟩` records `x` as the answer's witness, so counterexamples to inclusion or
equality are kept. **Nonempty is not nontrivial**: SAT of `member` says only that `L` has a
member; SAT and CSA together are *contingent*. An SAT witness never implies THM, and a
computational test of a few sentences is not a proof of a universal claim.

**Expected outcomes.** An instance's `expect` (`THM`, `CSA`, `OPN`, …) states what the
project expects. A refuted inclusion with `expect := CSA` is an expected negative result,
shown as such by the explorer rather than as a failure; `sil project check` warns only when a
summary contradicts its expectation.

**Unknown stays unknown.** Membership, emptiness, inclusion and equality are undecidable for
languages in general — for the languages of Wasm modules in particular. A problem with no
answer is unknown, and only an answer (a Lean proof, checked by the kernel) changes that.
Browsing a project never executes a module: the explorer reads the database only.

## The database and the explorer

`sil project sqlite` writes `language_domains`, `measures`, `language_interpretations`,
`languages` (with `identity` and `identity_hash`), `language_operands`,
`language_shape_roles`, and the view `language_problems`: each instance of a language shape
with the languages its arguments name (matched by their defining constants), its role (`L`,
`K`), expected status, summary and verdict. The explorer's Languages page reads these.

## Planned extensions (design)

These are not implemented; they record how the registry is meant to grow.

* **Encodings between domains.** A language over Unicode strings and one over bytes are
  related by an encoding, not equal. An `encoding` record would name a relation
  `R : T₁ → T₂ → Prop` between two domains (UTF-8 `String.utf8EncodeChar` lifted to lists, a
  number's decimal digits, a tree's event stream `JsonEvents.Tree.toEvents`), and `op :=
  image`/`preimage` would transport languages along it, with shapes stating that a language is
  the image of another. Functional, injective and total encodings would be properties proved
  once per encoding.
* **Partial equivalence relations and canonical forms.** Many formats identify presentations
  (JSON objects up to member order, CBOR up to argument width). A `language_per` record would
  name a PER `≈` on a domain with its proofs (symmetric, transitive); "`L` is closed under `≈`",
  "`L` and `K` are equal up to `≈`" and "`c` is a canonical form for `≈` on `L`" would be shapes,
  so that deterministic encodings (CBOR §4.2, canonical S-expressions) are languages with a
  normalization theorem rather than new kinds.
* **Tree languages.** Over a tree domain, a regular expression is the wrong presentation; tree
  automata or grammars over `JsonEvents.Tree` would be another `op`, with depth and size as
  measures, and the event-stream encoding as the bridge to byte and stream languages.
