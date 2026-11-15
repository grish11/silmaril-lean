module

public import Silmaril.Semantics.StreamBounds.Defs
public import Silmaril.Semantics.Accept.Defs
public import Silmaril.Semantics.Streams.Thms
public import Silmaril.Semantics.StreamMonitors.Thms
import Silmaril.Proofs.Semantics.StreamBounds.Finite
import Silmaril.Proofs.Semantics.StreamBounds.Infinite

/-!
# Resource bounds for streaming languages: theorems

Statements about `Silmaril.Semantics.StreamBounds.Defs`; longer proofs are in
`Silmaril.Proofs.Semantics.StreamBounds.Finite` and `.Infinite`.

* **Finite words.** `RunBound f n` is prefix-closed (`RunBound.of_isPrefix`) and monotone in
  `n` (`runBound_mono`), and every finite word lies within some bound (`iUnion_runBound`).
  The length instance is the whole-input bound `Accept.upTo List.length n Set.univ`
  (`runBound_length`, `runBound_length_eq_upTo`). A whole-input bound implies the item and
  depth bounds (`runBound_length_le_itemBound`, `runBound_length_le_depthBound`), but item
  bounds hold for words of every length (`replicate_mem_itemBound`). Without underflow the
  truncated depth is the net depth (`depth_eq_netDepth`).
* **Completeness relative to a bound.** `CorrectFold` is soundness plus completeness on
  `Set.univ` (`Acceptor.correctFold_iff`); completeness is antitone in the bound
  (`Acceptor.CompleteFoldOn.mono`), and completeness at every bound of an exhaustive family
  is full completeness on finite inputs (`Acceptor.completeFoldOn_univ_of_iUnion`,
  `Acceptor.completeFoldOn_univ_of_runBound`). `Acceptor.boundedReference L B` is sound for
  `L`, complete on `B` and `CorrectFold` for `L ⊓ B`, and is not complete on `Set.univ` as
  soon as some word of `L` is outside `B`.
* **Infinite words.** `safetyω (RunBound f n)` is a safety property
  (`isSafety_safetyω_runBound`). No infinite word meets a whole-input bound
  (`safetyω_runBound_length`). Infinite words whose separators recur within every window of
  `n + 1` symbols meet the item bound `n` (`mem_safetyω_itemBound_of_window`), for example
  the constant separator stream and `repeatItem item sep` with `item.length ≤ n`, so
  infinitely many bounded items form a nonempty safety property
  (`exists_mem_safetyω_itemBound_not_length`). A word that only opens leaves every depth
  bound (`not_mem_safetyω_depthBound`).
* **Transport bounds.** For `k ≥ 1`, every finite or infinite word is the limit of a stream
  whose chunks all have at most `k` symbols (`exists_chunkBound_limit`): a per-call ABI limit
  does not restrict the delivered language. With `k = 0` only the empty word is delivered
  (`limit_of_chunkBound_zero`).
-/

public section

namespace Silmaril.Streams

open Cslib

universe u v

variable {α : Type u} {τ : Type v}

/-! ## Running bounds on finite words -/

section Finite

variable {f g : List α → ℕ} {m n : ℕ}

@[simp] theorem mem_runBound {w : List α} : w ∈ RunBound f n ↔ ∀ p, p <+: w → f p ≤ n :=
  Iff.rfl

/-- Running bounds are prefix-closed. -/
theorem RunBound.of_isPrefix {w p : List α} (hw : w ∈ RunBound f n) (hp : p <+: w) :
    p ∈ RunBound f n :=
  fun q hq => hw q (hq.trans hp)

theorem RunBound.le {w : List α} (hw : w ∈ RunBound f n) : f w ≤ n := hw w (List.prefix_refl w)

/-- Membership of a running bound is decided by checking every prefix. -/
instance RunBound.decidableMem (f : List α → ℕ) (n : ℕ) : DecidablePred (· ∈ RunBound f n) :=
  fun w => decidable_of_iff (∀ p ∈ w.inits, f p ≤ n) (by simp [List.mem_inits])

instance ItemBound.decidableMem (isSep : α → Bool) (n : ℕ) :
    DecidablePred (· ∈ ItemBound isSep n) := RunBound.decidableMem _ _

instance DepthBound.decidableMem (kind : τ → BracketKind) (d : ℕ) :
    DecidablePred (· ∈ DepthBound kind d) := RunBound.decidableMem _ _

theorem runBound_mono (h : m ≤ n) : RunBound f m ≤ RunBound f n :=
  fun _ hw p hp => (hw p hp).trans h

/-- A smaller measure gives a weaker bound. -/
theorem runBound_mono_measure (h : ∀ w, f w ≤ g w) (n : ℕ) : RunBound g n ≤ RunBound f n :=
  Silmaril.Proofs.Semantics.StreamBounds.runBound_mono_measure h n

/-- Every finite word lies within some bound: the sum of the measures of its prefixes. -/
theorem mem_runBound_self (w : List α) : w ∈ RunBound f (w.inits.map f).sum :=
  Silmaril.Proofs.Semantics.StreamBounds.mem_runBound_self w

/-- Running bounds exhaust all finite words. -/
theorem iUnion_runBound (f : List α → ℕ) : ⋃ n, RunBound f n = Set.univ :=
  Silmaril.Proofs.Semantics.StreamBounds.iUnion_runBound f

/-- The length instance is the whole-input bound. -/
theorem runBound_length (n : ℕ) :
    RunBound (List.length : List α → ℕ) n = {w | w.length ≤ n} :=
  Silmaril.Proofs.Semantics.StreamBounds.runBound_length n

theorem runBound_length_eq_upTo (n : ℕ) :
    RunBound (List.length : List α → ℕ) n = Accept.upTo List.length n Set.univ := by
  rw [runBound_length]; ext w; simp [Accept.upTo]

theorem gap_nil (isSep : α → Bool) : gap isSep [] = 0 := rfl

theorem gap_append_singleton (isSep : α → Bool) (w : List α) (a : α) :
    gap isSep (w ++ [a]) = if isSep a then 0 else gap isSep w + 1 :=
  Silmaril.Proofs.Semantics.StreamBounds.gap_append_singleton isSep w a

theorem gap_le_length (isSep : α → Bool) (w : List α) : gap isSep w ≤ w.length :=
  Silmaril.Proofs.Semantics.StreamBounds.gap_le_length isSep w

theorem runBound_length_le_itemBound (isSep : α → Bool) (n : ℕ) :
    RunBound List.length n ≤ ItemBound isSep n :=
  runBound_mono_measure (gap_le_length isSep) n

/-- Item bounds do not bound the length: with a separator, words of every length have
items of size `0`. -/
theorem replicate_mem_itemBound (isSep : α → Bool) {sep : α} (h : isSep sep = true) (k : ℕ) :
    List.replicate k sep ∈ ItemBound isSep 0 :=
  Silmaril.Proofs.Semantics.StreamBounds.replicate_mem_itemBound isSep h k

theorem depth_nil (kind : τ → BracketKind) : depth kind [] = 0 := rfl

theorem depth_append_singleton (kind : τ → BracketKind) (w : List τ) (t : τ) :
    depth kind (w ++ [t]) = depthStep kind (depth kind w) t :=
  Silmaril.Proofs.Semantics.StreamBounds.depth_append_singleton kind w t

theorem depth_le_length (kind : τ → BracketKind) (w : List τ) : depth kind w ≤ w.length :=
  Silmaril.Proofs.Semantics.StreamBounds.depth_le_length kind w

theorem runBound_length_le_depthBound (kind : τ → BracketKind) (d : ℕ) :
    RunBound List.length d ≤ DepthBound kind d :=
  runBound_mono_measure (depth_le_length kind) d

/-- Without underflow, the truncated depth is the net depth. -/
theorem depth_eq_netDepth {kind : τ → BracketKind} {w : List τ}
    (h : ∀ p, p <+: w → 0 ≤ netDepth kind p) : (depth kind w : ℤ) = netDepth kind w :=
  Silmaril.Proofs.Semantics.StreamBounds.depth_eq_netDepth h

/-- A balanced word ends at depth `0`. -/
theorem Balanced.depth_eq_zero {kind : τ → BracketKind} {w : List τ} (h : w ∈ Balanced kind) :
    depth kind w = 0 := by
  have := depth_eq_netDepth h.1; rw [h.2] at this; exact_mod_cast this

end Finite

/-! ## Running bounds on infinite words -/

section Infinite

variable {f : List α → ℕ} {n : ℕ}

theorem mem_safetyω_runBound {s : ωSequence α} :
    s ∈ safetyω (RunBound f n) ↔ ∀ k, f (s.take k) ≤ n :=
  Silmaril.Proofs.Semantics.StreamBounds.mem_safetyω_runBound

theorem isSafety_safetyω_runBound (f : List α → ℕ) (n : ℕ) :
    (safetyω (RunBound f n)).IsSafety :=
  isSafety_safetyω _

/-- No infinite word satisfies a whole-input bound. -/
theorem safetyω_runBound_length (m : ℕ) :
    safetyω (RunBound (List.length : List α → ℕ) m) = ⊥ :=
  Silmaril.Proofs.Semantics.StreamBounds.safetyω_runBound_length m

/-- An infinite word meets the item bound `n` if every window of `n + 1` consecutive
positions contains a separator. -/
theorem mem_safetyω_itemBound_of_window {isSep : α → Bool} {s : ωSequence α}
    (h : ∀ i, ∃ j, i ≤ j ∧ j ≤ i + n ∧ isSep (s j) = true) :
    s ∈ safetyω (ItemBound isSep n) :=
  Silmaril.Proofs.Semantics.StreamBounds.mem_safetyω_itemBound_of_window h

theorem const_mem_safetyω_itemBound {isSep : α → Bool} {sep : α} (h : isSep sep = true)
    (n : ℕ) : ωSequence.const sep ∈ safetyω (ItemBound isSep n) :=
  Silmaril.Proofs.Semantics.StreamBounds.const_mem_safetyω_itemBound h n

/-- Repeating one item of at most `n` symbols and a separator meets the item bound `n`.
Separators inside `item` are allowed; they only shorten items. -/
theorem repeatItem_mem_safetyω_itemBound {isSep : α → Bool} {item : List α} {sep : α}
    (h : isSep sep = true) (hn : item.length ≤ n) :
    repeatItem item sep ∈ safetyω (ItemBound isSep n) :=
  Silmaril.Proofs.Semantics.StreamBounds.repeatItem_mem_safetyω_itemBound h hn

/-- With a separator, some infinite word meets every item bound but no whole-input bound:
unboundedly many bounded items. -/
theorem exists_mem_safetyω_itemBound_not_length {isSep : α → Bool} {sep : α}
    (h : isSep sep = true) :
    ∃ s : ωSequence α, (∀ n, s ∈ safetyω (ItemBound isSep n)) ∧
      ∀ m, s ∉ safetyω (RunBound List.length m) :=
  ⟨_, const_mem_safetyω_itemBound h, fun m hs => by
    rw [safetyω_runBound_length] at hs; exact ωLanguage.notMem_bot _ hs⟩

/-- A word that only opens leaves every depth bound. -/
theorem not_mem_safetyω_depthBound {kind : τ → BracketKind} {s : ωSequence τ}
    (h : ∀ i, kind (s i) = .opening) (d : ℕ) : s ∉ safetyω (DepthBound kind d) :=
  Silmaril.Proofs.Semantics.StreamBounds.not_mem_safetyω_depthBound h d

end Infinite

/-! ## Transport bounds -/

theorem ChunkBound.mono {k l : ℕ} {cs : Chunks α} (h : ChunkBound k cs) (hkl : k ≤ l) :
    ChunkBound l cs :=
  fun n => (h n).trans hkl

theorem chunkBound_ofω (s : ωSequence α) : ChunkBound 1 (Chunks.ofω s) := fun _ => le_rfl

theorem chunkBound_ofList_singletons (w : List α) :
    ChunkBound 1 (Chunks.ofList (w.map fun a => [a])) :=
  Silmaril.Proofs.Semantics.StreamBounds.chunkBound_ofList_singletons w

theorem limit_ofList_singletons (w : List α) :
    (Chunks.ofList (w.map fun a => [a])).limit = .fin w :=
  Silmaril.Proofs.Semantics.StreamBounds.limit_ofList_singletons w

/-- A per-chunk limit `k ≥ 1` does not restrict the delivered language: every finite or
infinite word is the limit of a stream of chunks of at most `k` symbols. -/
theorem exists_chunkBound_limit {k : ℕ} (hk : 1 ≤ k) (t : Word α) :
    ∃ cs : Chunks α, ChunkBound k cs ∧ cs.limit = t :=
  Silmaril.Proofs.Semantics.StreamBounds.exists_chunkBound_limit hk t

/-- Chunks of `0` symbols only deliver the empty word. -/
theorem limit_of_chunkBound_zero {cs : Chunks α} (h : ChunkBound 0 cs) : cs.limit = .fin [] :=
  Silmaril.Proofs.Semantics.StreamBounds.limit_of_chunkBound_zero h

end Silmaril.Streams

namespace Silmaril.Acceptor

open Silmaril.Streams

universe w x y

variable {σ : Type w} {χ : Type x} {α : Type y} [ChunkView χ α]

/-- `CorrectFold` is soundness plus completeness on every input. -/
theorem correctFold_iff (A : Acceptor σ χ) (L : Language α) [DecidablePred (· ∈ L)] :
    A.CorrectFold L ↔ A.SoundFold L ∧ A.CompleteFoldOn L Set.univ :=
  Silmaril.Proofs.Semantics.StreamBounds.correctFold_iff A L

/-- Completeness on a bound gives completeness on every smaller bound. -/
theorem CompleteFoldOn.mono {A : Acceptor σ χ} {L B B' : Language α}
    (h : A.CompleteFoldOn L B) (hB : B' ≤ B) : A.CompleteFoldOn L B' :=
  fun cs hL hB' => h cs hL (hB hB')

/-- Completeness on every member of an exhaustive family of bounds is full completeness. -/
theorem completeFoldOn_univ_of_iUnion {A : Acceptor σ χ} {L : Language α} {ι : Sort*}
    {B : ι → Language α} (hB : ⋃ i, B i = Set.univ) (h : ∀ i, A.CompleteFoldOn L (B i)) :
    A.CompleteFoldOn L Set.univ :=
  Silmaril.Proofs.Semantics.StreamBounds.completeFoldOn_univ_of_iUnion hB h

/-- Completeness at every running bound is full completeness on finite inputs. -/
theorem completeFoldOn_univ_of_runBound {A : Acceptor σ χ} {L : Language α}
    (f : List α → ℕ) (h : ∀ n, A.CompleteFoldOn L (RunBound f n)) :
    A.CompleteFoldOn L Set.univ :=
  completeFoldOn_univ_of_iUnion (iUnion_runBound f) h

theorem boundedReference_correctFold (L B : Language α) [DecidablePred (· ∈ L)]
    [DecidablePred (· ∈ B)] : (boundedReference (χ := χ) L B).CorrectFold (L ⊓ B) :=
  Silmaril.Proofs.Semantics.StreamBounds.boundedReference_correctFold L B

theorem boundedReference_soundFold (L B : Language α) [DecidablePred (· ∈ L)]
    [DecidablePred (· ∈ B)] : (boundedReference (χ := χ) L B).SoundFold L :=
  Silmaril.Proofs.Semantics.StreamBounds.boundedReference_soundFold L B

theorem boundedReference_completeFoldOn (L B : Language α) [DecidablePred (· ∈ L)]
    [DecidablePred (· ∈ B)] : (boundedReference (χ := χ) L B).CompleteFoldOn L B :=
  Silmaril.Proofs.Semantics.StreamBounds.boundedReference_completeFoldOn L B

/-- A word of `L` outside the bound `B` shows that the bounded reference is not complete. -/
theorem boundedReference_not_completeFoldOn_univ {L B : Language α} [DecidablePred (· ∈ L)]
    [DecidablePred (· ∈ B)] {w : List α} (hL : w ∈ L) (hB : w ∉ B) :
    ¬ (boundedReference (χ := List α) L B).CompleteFoldOn L Set.univ :=
  Silmaril.Proofs.Semantics.StreamBounds.boundedReference_not_completeFoldOn_univ hL hB

end Silmaril.Acceptor
