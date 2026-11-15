module

public import Silmaril.Semantics.Streams.Defs
import Silmaril.Proofs.Semantics.Streams.Limit

/-!
# Finite, infinite and chunked streams: theorems

Statements about `Silmaril.Semantics.Streams.Defs`; longer proofs are in
`Silmaril.Proofs.Semantics.Streams.Limit`.

* Finite and infinite words embed into `Word α` with complementary ranges
  (`Word.isCompl_range`). Infinite words do not inject into finite words
  (`Word.not_injective_ωSequence_list`), so the direction of the embedding matters.
* Every chunk stream has exactly one limit (`Chunks.limit_spec`, `Chunks.Limit.unique`).
  The limit is infinite exactly when the stream is progressive
  (`Chunks.isInfinite_limit_iff`). This is the empty-chunk caveat: a stream may run
  forever and still only deliver a finite word.
* Rechunking (splitting, merging, inserting or deleting empty chunks) preserves the
  limit whenever delivered prefixes are mutually cofinal (`Chunks.limit_eq_of_cofinal`).
* Terminating chunk sequences deliver their `List.flatten` (`Chunks.limit_ofList`),
  letter-at-a-time streams deliver their word (`Chunks.limit_ofω`), and streams of
  nonempty chunks deliver CSLib's `ωSequence.flatten` (`Chunks.limit_eq_flatten`).
-/

public section

namespace Silmaril.Streams

open Cslib

universe u

variable {α : Type u}

namespace Word

theorem isCompl_range :
    IsCompl (Set.range (ofList : List α ↪ Word α)) (Set.range (ofω : ωSequence α ↪ Word α)) :=
  Silmaril.Proofs.Semantics.Streams.isCompl_range

/-- There is no injection from infinite words into finite words, already over `Bool`. -/
theorem not_injective_ωSequence_list (f : ωSequence Bool → List Bool) : ¬ f.Injective :=
  Silmaril.Proofs.Semantics.Streams.not_injective_ωSequence_list f

/-- Prefixes of a prefix are prefixes. -/
theorem HasPrefix.of_isPrefix {t : Word α} {p q : List α} (hp : t.HasPrefix p)
    (hq : q <+: p) : t.HasPrefix q :=
  Silmaril.Proofs.Semantics.Streams.hasPrefix_of_isPrefix hp hq

end Word

namespace Lang

@[simp] theorem mem_finPart {L : Lang α} {w : List α} : w ∈ L.finPart ↔ Word.fin w ∈ L :=
  Iff.rfl

@[simp] theorem mem_ωPart {L : Lang α} {s : ωSequence α} : s ∈ L.ωPart ↔ Word.inf s ∈ L :=
  Iff.rfl

end Lang

namespace Chunks

@[simp] theorem prefixAt_zero (cs : Chunks α) : cs.prefixAt 0 = [] := rfl

theorem prefixAt_succ (cs : Chunks α) (n : ℕ) :
    cs.prefixAt (n + 1) = cs.prefixAt n ++ cs n :=
  Silmaril.Proofs.Semantics.Streams.prefixAt_succ cs n

/-- Delivered input only grows. -/
theorem prefixAt_mono (cs : Chunks α) {m n : ℕ} (h : m ≤ n) :
    cs.prefixAt m <+: cs.prefixAt n :=
  Silmaril.Proofs.Semantics.Streams.prefixAt_mono cs h

theorem Limit.unique {cs : Chunks α} {t t' : Word α} (h : cs.Limit t) (h' : cs.Limit t') :
    t = t' :=
  Silmaril.Proofs.Semantics.Streams.limit_unique h h'

theorem limit_spec (cs : Chunks α) : cs.Limit cs.limit :=
  Silmaril.Proofs.Semantics.Streams.limit_spec cs

theorem limit_eq_iff {cs : Chunks α} {t : Word α} : cs.limit = t ↔ cs.Limit t :=
  Silmaril.Proofs.Semantics.Streams.limit_eq_iff

/-- Progress (infinitely many nonempty chunks) is exactly what makes the limit infinite. -/
theorem isInfinite_limit_iff (cs : Chunks α) : cs.limit.IsInfinite ↔ cs.Progressive :=
  Silmaril.Proofs.Semantics.Streams.isInfinite_limit_iff cs

theorem isFinite_limit_iff (cs : Chunks α) : cs.limit.IsFinite ↔ ¬ cs.Progressive :=
  Silmaril.Proofs.Semantics.Streams.isFinite_limit_iff cs

/-- A progressive stream delivers arbitrarily long prefixes. -/
theorem Progressive.unbounded {cs : Chunks α} (h : cs.Progressive) (k : ℕ) :
    ∃ n, k ≤ (cs.prefixAt n).length :=
  Silmaril.Proofs.Semantics.Streams.unbounded_of_progressive h k

/-- A stream without progress eventually stops delivering input. -/
theorem eventually_const_of_not_progressive {cs : Chunks α} (h : ¬ cs.Progressive) :
    ∃ N, ∀ n, N ≤ n → cs.prefixAt n = cs.prefixAt N :=
  Silmaril.Proofs.Semantics.Streams.eventually_const_of_not_progressive h

/-- Rechunking: mutually cofinal delivered prefixes give the same limit. -/
theorem limit_eq_of_cofinal {cs cs' : Chunks α}
    (h₁ : ∀ n, ∃ m, cs.prefixAt n <+: cs'.prefixAt m)
    (h₂ : ∀ m, ∃ n, cs'.prefixAt m <+: cs.prefixAt n) : cs.limit = cs'.limit :=
  Silmaril.Proofs.Semantics.Streams.limit_eq_of_cofinal h₁ h₂

theorem prefixAt_ofList (cs : List (List α)) (n : ℕ) :
    (ofList cs).prefixAt n = (cs.take n).flatten :=
  Silmaril.Proofs.Semantics.Streams.prefixAt_ofList cs n

/-- A terminating chunk sequence delivers its concatenation. -/
theorem limit_ofList (cs : List (List α)) : (ofList cs).limit = .fin cs.flatten :=
  Silmaril.Proofs.Semantics.Streams.limit_ofList cs

theorem prefixAt_ofω (s : ωSequence α) (n : ℕ) : (ofω s).prefixAt n = s.take n :=
  Silmaril.Proofs.Semantics.Streams.prefixAt_ofω s n

/-- One letter per chunk delivers the word itself. -/
theorem limit_ofω (s : ωSequence α) : (ofω s).limit = .inf s :=
  Silmaril.Proofs.Semantics.Streams.limit_ofω s

/-- Nonempty chunks deliver CSLib's `ωSequence.flatten`. -/
theorem limit_eq_flatten [Inhabited α] {cs : Chunks α} (h : ∀ k, cs k ≠ []) :
    cs.limit = .inf cs.flatten :=
  Silmaril.Proofs.Semantics.Streams.limit_eq_flatten h

theorem accepts_ofList {L : Lang α} (cs : List (List α)) :
    Accepts L (ofList cs) ↔ cs.flatten ∈ L.finPart := by
  rw [Accepts, limit_ofList]; rfl

theorem accepts_ofω {L : Lang α} (s : ωSequence α) : Accepts L (ofω s) ↔ s ∈ L.ωPart := by
  rw [Accepts, limit_ofω]; rfl

/-- A stream that stalls on empty chunks is judged by the finite part of the language. -/
theorem accepts_of_not_progressive {L : Lang α} {cs : Chunks α} (h : ¬ cs.Progressive) :
    ∃ w, cs.limit = .fin w ∧ (Accepts L cs ↔ w ∈ L.finPart) := by
  cases hl : cs.limit with
  | fin w => exact ⟨w, rfl, by rw [Accepts, hl]; rfl⟩
  | inf s => exact absurd ((isInfinite_limit_iff cs).mp (by rw [hl]; exact id)) h

end Chunks

end Silmaril.Streams
