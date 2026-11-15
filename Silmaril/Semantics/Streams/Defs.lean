module

public import Cslib.Computability.Languages.OmegaLanguage
public import Mathlib.Computability.Language
public import Mathlib.Logic.Embedding.Basic

/-!
# Finite, infinite and chunked streams

Vocabulary for languages of inputs that arrive incrementally, independent of any
concrete execution model. It reuses Mathlib's `Language α` (sets of finite words,
`Set (List α)`) and CSLib's `ωSequence α` and `ωLanguage α` (infinite words and
sets of them), and adds:

* `Word α`: a *finite or infinite* word, the set `A^∞ = A^* ∪ A^ω` of Perrin and Pin,
  *Infinite Words* (2004), §I.1. Finite words (`Word.ofList`) and infinite words
  (`Word.ofω`) both embed into it, with disjoint ranges that cover it.
  There is no injection the other way round from infinite into finite words for an
  arbitrary alphabet, so `Word α` is where finite and infinite inputs meet.
* `Lang α`: an ∞-language, a set of finite or infinite words. It is equivalent to a
  pair of a `Language α` (its finite part) and an `ωLanguage α` (its infinite part).
* `Chunks α = ωSequence (List α)`: an unbounded stream of chunks, as delivered by a
  `process(chunk)` interface. Chunks may be empty. `Chunks.prefixAt cs n` is the input
  delivered by the first `n` chunks.
* `Chunks.Limit cs t`: `t` is the word the chunk stream delivers in the limit. It is
  infinite exactly when the stream is `Progressive` (infinitely many nonempty chunks)
  and finite otherwise: a stream that stalls on empty chunks forever delivers only a
  finite word, however long it runs.
* `Chunks.ofList` embeds a terminating chunk sequence (padding with empty chunks) and
  `Chunks.ofω` chunks an infinite word one element at a time.

Theorems are in `Silmaril.Semantics.Streams.Thms`.

## Scope

These are definitions about data, not about any machine: nothing here says that a
particular program or Wasm component reads its input this way. A concrete bridge
instantiates the alphabet (for bytes, `α = UInt8`) and proves that its execution
produces these chunk streams.
-/

@[expose] public section

namespace Silmaril.Streams

open Cslib

universe u

variable {α : Type u}

/-! ## Finite or infinite words -/

/-- A finite or infinite word over `α`. -/
inductive Word (α : Type u) where
  /-- A finite word. -/
  | fin (w : List α)
  /-- An infinite word. -/
  | inf (s : ωSequence α)

namespace Word

instance : Inhabited (Word α) := ⟨fin []⟩

/-- Finite words embed into finite-or-infinite words. -/
def ofList : List α ↪ Word α := ⟨fin, fun _ _ h => by cases h; rfl⟩

/-- Infinite words embed into finite-or-infinite words. -/
def ofω : ωSequence α ↪ Word α := ⟨inf, fun _ _ h => by cases h; rfl⟩

/-- The word is finite. -/
def IsFinite : Word α → Prop
  | fin _ => True
  | inf _ => False

/-- The word is infinite. -/
def IsInfinite (t : Word α) : Prop := ¬ t.IsFinite

/-- `p` is a finite prefix of `t`. -/
def HasPrefix : Word α → List α → Prop
  | fin w, p => p <+: w
  | inf s, p => s.take p.length = p

/-- Prepend a finite word. -/
def prepend (p : List α) : Word α → Word α
  | fin w => fin (p ++ w)
  | inf s => inf (p ++ω s)

/-- Map every letter. -/
def map {β : Type*} (f : α → β) : Word α → Word β
  | fin w => fin (w.map f)
  | inf s => inf (s.map f)

end Word

/-! ## ∞-languages -/

/-- An ∞-language: a set of finite or infinite words. -/
abbrev Lang (α : Type u) := Set (Word α)

namespace Lang

/-- The finite words of an ∞-language. -/
def finPart (L : Lang α) : Language α := {w | Word.fin w ∈ L}

/-- The infinite words of an ∞-language. -/
def ωPart (L : Lang α) : ωLanguage α := ⟨{s | Word.inf s ∈ L}⟩

/-- The ∞-language with the given finite part and no infinite words. -/
def ofLanguage (L : Language α) : Lang α := {t | ∃ w ∈ L, t = Word.fin w}

/-- The ∞-language with the given infinite part and no finite words. -/
def ofωLanguage (p : ωLanguage α) : Lang α := {t | ∃ s ∈ p, t = Word.inf s}

/-- The ∞-language with a given finite part and a given infinite part. -/
def mk (L : Language α) (p : ωLanguage α) : Lang α := ofLanguage L ∪ ofωLanguage p

/-- An ∞-language is the same as its finite and its infinite part. -/
def equiv : Lang α ≃ Language α × ωLanguage α where
  toFun L := (L.finPart, L.ωPart)
  invFun P := mk P.1 P.2
  left_inv L := by
    ext (w | s) <;> simp [mk, ofLanguage, ofωLanguage, finPart, ωPart] <;> exact Iff.rfl
  right_inv P := by
    obtain ⟨L, p⟩ := P
    simp only [Prod.mk.injEq]
    refine ⟨?_, ?_⟩
    · ext w; simp [mk, ofLanguage, ofωLanguage, finPart]; exact Iff.rfl
    · ext s; simp [mk, ofLanguage, ofωLanguage, ωPart]; exact Iff.rfl

end Lang

/-! ## Chunk streams -/

/-- An unbounded stream of (possibly empty) chunks. -/
abbrev Chunks (α : Type u) := ωSequence (List α)

namespace Chunks

/-- The input delivered by the first `n` chunks. -/
def prefixAt (cs : Chunks α) (n : ℕ) : List α := (cs.take n).flatten

/-- Infinitely many chunks are nonempty: the stream makes progress. -/
def Progressive (cs : Chunks α) : Prop := ∀ N, ∃ n, N ≤ n ∧ cs n ≠ []

/-- `t` is the word that the chunk stream delivers in the limit.

A finite `t` is reached after finitely many chunks and never extended; an infinite `t`
extends every delivered prefix, and the delivered prefixes grow without bound. -/
def Limit (cs : Chunks α) : Word α → Prop
  | .fin w => ∃ N, ∀ n, N ≤ n → cs.prefixAt n = w
  | .inf s => (∀ n, (Word.inf s).HasPrefix (cs.prefixAt n)) ∧
      ∀ k, ∃ n, k ≤ (cs.prefixAt n).length

/-- The word delivered in the limit (it exists and is unique: `Chunks.limit_spec`,
`Chunks.Limit.unique`). -/
noncomputable def limit (cs : Chunks α) : Word α := Classical.epsilon cs.Limit

/-- A terminating chunk sequence, padded with empty chunks forever. -/
def ofList (cs : List (List α)) : Chunks α := fun n => cs.getD n []

/-- An infinite word, one letter per chunk. -/
def ofω (s : ωSequence α) : Chunks α := fun n => [s n]

/-- The chunk stream accepted by an ∞-language: its limit word is in the language. -/
def Accepts (L : Lang α) (cs : Chunks α) : Prop := cs.limit ∈ L

end Chunks

end Silmaril.Streams
