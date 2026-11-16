module

public import Silmaril.Project.Defs

/-!
# Standard problem shapes: languages

The questions a project asks about its languages, as problems over arguments. Each shape keeps
the *sentence* `x` as its last argument, so that an instance which fixes the languages (and
measures and bounds) but not `x` is a problem over the domain, and its SZS statuses are the
usual questions (`Silmaril.Project.Shapes.Language.Thms` proves each reading):

| name | statement | THM | SAT | UNS | CSA |
|---|---|---|---|---|---|
| `silmaril.shapes.language.member` | `Member L x`: `x ∈ L` | `L` is universal | `L` is nonempty | `L` is empty | `L` is not universal |
| `silmaril.shapes.language.subset_at` | `SubsetAt L K x`: `x ∈ L → x ∈ K` | `L ⊆ K` | | | a counterexample `x ∈ L \ K` |
| `silmaril.shapes.language.eq_at` | `EqAt L K x`: `x ∈ L ↔ x ∈ K` | `L = K` | | | a counterexample in the symmetric difference |
| `silmaril.shapes.language.bound_at` | `BoundAt L μ b x`: `x ∈ L → μ x ≤ b` | every member has `μ x ≤ b` | | | a member with `μ x > b` |
| `silmaril.shapes.language.eq_within_at` | `EqWithinAt L K μ b x`: `x ∈ L ↔ x ∈ K ∧ μ x ≤ b` | `L` is `K` restricted to `μ ≤ b` | | | a counterexample |
| `silmaril.shapes.language.bytes_member` | `BytesMember L b`: the bytes `b` are in `L` | | | | |

Fixing `x` too gives a closed problem: **sentence membership**, THM when `x ∈ L` and CSA when
`x ∉ L` (at arity 0 an UNS answer is a CSA). `bytes_member` is **artifact membership**: given a
registered value of format `bytes` for `b`, the instance is about the CID-pinned file. A problem
with no answer is unknown, whatever the language: membership, emptiness, inclusion and
equality are undecidable for languages in general (for instance for the languages of Wasm
modules), so an unknown status means only that no proof has been given.

**Directions.** `subset_at L K` is the refinement `L ⊑ K` (every sentence of `L` is one of `K`);
the converse is the instance with the arguments swapped. A CSA answer of `subset_at`,
`eq_at`, `bound_at` or `eq_within_at` whose proof is a literal `⟨x, h⟩` records `x` as its
witness: the counterexample is kept with the answer.

**Nonempty is not nontrivial.** SAT of `member L` says only that `L` has a member; that `L` is
also not universal is the separate CSA answer (SAT and CSA together are *contingent*). An SAT
answer never implies THM.

The domains `bytes` (`List UInt8`), `unicode` (`List Char`: strings of Unicode scalar values),
`nat` (`ℕ`), `nat.additive` (`Multiplicative ℕ`, the monoid `(ℕ, +)` for regular expressions
over numbers), `nat.lists` (`List ℕ`) and the measures `bytes.length`, `unicode.length`,
`unicode.utf8_length` (bytes of the UTF-8 encoding), `nat.value` and `nat.lists.length` are
registered here. A project registers its own with `silmaril language_domain` and
`silmaril measure`.
-/

@[expose] public section

namespace Silmaril.Project.Shapes

/-- **`x` is in `L`.** -/
@[problem "silmaril.shapes.language.member" (title := "A sentence is in a language")]
def Member {α : Type} (L : Set α) (x : α) : Prop := x ∈ L

/-- **The bytes `b` are in the byte language `L`.** -/
@[problem "silmaril.shapes.language.bytes_member" (title := "An artifact's bytes are in a byte language")]
def BytesMember (L : Set (List UInt8)) (b : Silmaril.Formats.Bytes) : Prop := b.toList ∈ L

/-- **Inclusion at `x`**: if `x ∈ L` then `x ∈ K`. -/
@[problem "silmaril.shapes.language.subset_at" (title := "A language is included in another")]
def SubsetAt {α : Type} (L K : Set α) (x : α) : Prop := x ∈ L → x ∈ K

/-- **Equality at `x`**: `x ∈ L` iff `x ∈ K`. -/
@[problem "silmaril.shapes.language.eq_at" (title := "Two languages are equal")]
def EqAt {α : Type} (L K : Set α) (x : α) : Prop := x ∈ L ↔ x ∈ K

/-- **A measure bound at `x`**: if `x ∈ L` then `μ x ≤ b`. -/
@[problem "silmaril.shapes.language.bound_at" (title := "Every member of a language is bounded")]
def BoundAt {α : Type} (L : Set α) (μ : α → ℕ) (b : ℕ) (x : α) : Prop := x ∈ L → μ x ≤ b

/-- **Equality with a measure-restricted language at `x`**: `x ∈ L` iff `x ∈ K ∧ μ x ≤ b`. -/
@[problem "silmaril.shapes.language.eq_within_at"
  (title := "A language is another restricted by a measure bound")]
def EqWithinAt {α : Type} (L K : Set α) (μ : α → ℕ) (b : ℕ) (x : α) : Prop :=
  x ∈ L ↔ x ∈ K ∧ μ x ≤ b

end Silmaril.Project.Shapes

namespace Silmaril.Project.Languages

/-- The domain of byte strings. -/
abbrev Bytes : Type := List UInt8
/-- The domain of strings of Unicode scalar values (Lean's `Char` is a scalar value). -/
abbrev Unicode : Type := List Char
/-- The domain of natural numbers. -/
abbrev Naturals : Type := ℕ
/-- The monoid `(ℕ, +, 0)`, for regular expressions over numbers. -/
abbrev NatAdditive : Type := Multiplicative ℕ
/-- The domain of lists of natural numbers. -/
abbrev NatLists : Type := List ℕ

/-- The number of bytes. -/
def bytesLength (w : List UInt8) : ℕ := w.length
/-- The number of scalar values. -/
def unicodeLength (s : List Char) : ℕ := s.length
/-- The number of bytes of the UTF-8 encoding. -/
def unicodeUtf8Length (s : List Char) : ℕ := (s.map Char.utf8Size).sum
/-- A number itself. -/
def natValue (n : ℕ) : ℕ := n
/-- The number of elements. -/
def natListsLength (l : List ℕ) : ℕ := l.length

end Silmaril.Project.Languages

silmaril language_domain bytes := Silmaril.Project.Languages.Bytes
  (doc := "Byte strings, List UInt8 (Mathlib's Language UInt8 is Set (List UInt8))")
silmaril language_domain unicode := Silmaril.Project.Languages.Unicode
  (doc := "Strings of Unicode scalar values, List Char")
silmaril language_domain nat := Silmaril.Project.Languages.Naturals
  (doc := "Natural numbers")
silmaril language_domain nat.additive := Silmaril.Project.Languages.NatAdditive
  (doc := "Natural numbers as the monoid (ℕ, +, 0), Multiplicative ℕ")
silmaril language_domain nat.lists := Silmaril.Project.Languages.NatLists
  (doc := "Finite sequences of natural numbers, List ℕ")

silmaril measure bytes.length := Silmaril.Project.Languages.bytesLength (domain := bytes)
  (doc := "The number of bytes")
silmaril measure unicode.length := Silmaril.Project.Languages.unicodeLength (domain := unicode)
  (doc := "The number of scalar values")
silmaril measure unicode.utf8_length := Silmaril.Project.Languages.unicodeUtf8Length
  (domain := unicode) (doc := "The number of bytes of the UTF-8 encoding")
silmaril measure nat.value := Silmaril.Project.Languages.natValue (domain := nat)
  (doc := "The number itself")
silmaril measure nat.lists.length := Silmaril.Project.Languages.natListsLength (domain := nat.lists)
  (doc := "The number of elements")
