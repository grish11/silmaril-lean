module

public import Silmaril.Semantics.Streams.Defs
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Encodable.Basic
import Mathlib.Logic.Function.Basic

/-! # Proofs: chunk limits and finite-or-infinite words -/

@[expose] public section

namespace Silmaril.Proofs.Semantics.Streams

open Cslib Silmaril.Streams

universe u

variable {α : Type u}

/-! ## Prefixes of words -/

theorem hasPrefix_of_isPrefix {t : Word α} {p q : List α} (hp : t.HasPrefix p) (hq : q <+: p) :
    t.HasPrefix q := by
  cases t with
  | fin w => exact hq.trans hp
  | inf s =>
    simp only [Word.HasPrefix] at hp ⊢
    have hlen := hq.length_le
    rw [List.prefix_iff_eq_take] at hq
    rw [hq, List.length_take, Nat.min_eq_left hlen, ← hp, ωSequence.take_take,
      Nat.min_eq_right hlen]

/-! ## Delivered prefixes -/

theorem prefixAt_zero (cs : Chunks α) : cs.prefixAt 0 = [] := rfl

theorem prefixAt_succ (cs : Chunks α) (n : ℕ) :
    cs.prefixAt (n + 1) = cs.prefixAt n ++ cs n := by
  rw [Chunks.prefixAt, Chunks.prefixAt, ωSequence.take_succ', List.flatten_append]
  simp

theorem prefixAt_mono (cs : Chunks α) {m n : ℕ} (h : m ≤ n) :
    cs.prefixAt m <+: cs.prefixAt n := by
  induction n, h using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ n _ ih => exact ih.trans (by rw [prefixAt_succ]; exact List.prefix_append _ _)

theorem length_prefixAt_mono (cs : Chunks α) {m n : ℕ} (h : m ≤ n) :
    (cs.prefixAt m).length ≤ (cs.prefixAt n).length :=
  (prefixAt_mono cs h).length_le

/-- A progressive stream delivers arbitrarily long prefixes. -/
theorem unbounded_of_progressive {cs : Chunks α} (h : cs.Progressive) (k : ℕ) :
    ∃ n, k ≤ (cs.prefixAt n).length := by
  induction k with
  | zero => exact ⟨0, Nat.zero_le _⟩
  | succ k ih =>
    obtain ⟨n, hn⟩ := ih
    obtain ⟨m, hm, hne⟩ := h n
    refine ⟨m + 1, ?_⟩
    have h1 := length_prefixAt_mono cs hm
    have h2 : 0 < (cs m).length := List.length_pos_iff.mpr hne
    rw [prefixAt_succ, List.length_append]
    omega

/-- A stream that is not progressive is eventually constant. -/
theorem eventually_const_of_not_progressive {cs : Chunks α} (h : ¬ cs.Progressive) :
    ∃ N, ∀ n, N ≤ n → cs.prefixAt n = cs.prefixAt N := by
  simp only [Chunks.Progressive, not_forall, not_exists, not_and, not_not] at h
  obtain ⟨N, hN⟩ := h
  refine ⟨N, fun n hn => ?_⟩
  induction n, hn using Nat.le_induction with
  | base => rfl
  | succ n hn ih => rw [prefixAt_succ, hN n hn, List.append_nil, ih]

/-! ## Limits -/

theorem limit_unique {cs : Chunks α} {t t' : Word α} (h : cs.Limit t) (h' : cs.Limit t') :
    t = t' := by
  -- A finite limit bounds every delivered prefix, an infinite one does not.
  have finInf : ∀ {w : List α} {s : ωSequence α}, cs.Limit (.fin w) → cs.Limit (.inf s) →
      False := by
    intro w s ⟨N, hN⟩ ⟨_, hunb⟩
    obtain ⟨n, hn⟩ := hunb (w.length + 1)
    have hle := length_prefixAt_mono cs (Nat.le_max_left n N)
    rw [hN _ (Nat.le_max_right n N)] at hle
    omega
  cases t with
  | fin w =>
    cases t' with
    | fin w' =>
      obtain ⟨N, hN⟩ := h
      obtain ⟨N', hN'⟩ := h'
      rw [← hN (max N N') (Nat.le_max_left _ _), hN' (max N N') (Nat.le_max_right _ _)]
    | inf s' => exact (finInf h h').elim
  | inf s =>
    cases t' with
    | fin w' => exact (finInf h' h).elim
    | inf s' =>
      obtain ⟨hp, hunb⟩ := h
      obtain ⟨hp', _⟩ := h'
      congr 1
      apply ωSequence.take_theorem
      intro k
      obtain ⟨n, hn⟩ := hunb k
      have e : s.take (cs.prefixAt n).length = s'.take (cs.prefixAt n).length :=
        (hp n).trans (hp' n).symm
      have := congrArg (List.take k) e
      rwa [ωSequence.take_take, ωSequence.take_take, Nat.min_eq_right hn] at this

/-- A progressive stream has an infinite limit. -/
theorem exists_limit_inf {cs : Chunks α} (h : cs.Progressive) : ∃ s, cs.Limit (.inf s) := by
  have hunb := unbounded_of_progressive h
  let idx : ℕ → ℕ := fun k => Classical.choose (hunb (k + 1))
  have hidx : ∀ k, k < (cs.prefixAt (idx k)).length := fun k =>
    Classical.choose_spec (hunb (k + 1))
  let s : ωSequence α := fun k => (cs.prefixAt (idx k))[k]'(hidx k)
  -- Any two delivered prefixes agree where both are defined.
  have agree : ∀ m n k (hm : k < (cs.prefixAt m).length) (hn : k < (cs.prefixAt n).length),
      (cs.prefixAt m)[k] = (cs.prefixAt n)[k] := by
    intro m n k hm hn
    rw [(prefixAt_mono cs (Nat.le_max_left m n)).getElem hm,
      (prefixAt_mono cs (Nat.le_max_right m n)).getElem hn]
  refine ⟨s, fun n => ?_, hunb⟩
  show s.take (cs.prefixAt n).length = cs.prefixAt n
  apply List.ext_getElem (by simp [ωSequence.length_take])
  intro k hk hk'
  have := ωSequence.getElem?_take (s := s) (k := k) (n := (cs.prefixAt n).length) hk'
  rw [List.getElem?_eq_getElem hk] at this
  rw [Option.some.inj this]
  exact agree _ _ _ _ _

theorem exists_limit (cs : Chunks α) : ∃ t, cs.Limit t := by
  by_cases h : cs.Progressive
  · obtain ⟨s, hs⟩ := exists_limit_inf h
    exact ⟨_, hs⟩
  · obtain ⟨N, hN⟩ := eventually_const_of_not_progressive h
    exact ⟨.fin (cs.prefixAt N), N, hN⟩

theorem limit_spec (cs : Chunks α) : cs.Limit cs.limit :=
  Classical.epsilon_spec (exists_limit cs)

theorem limit_eq_iff {cs : Chunks α} {t : Word α} : cs.limit = t ↔ cs.Limit t :=
  ⟨fun h => h ▸ limit_spec cs, fun h => limit_unique (limit_spec cs) h⟩

theorem isInfinite_limit_iff (cs : Chunks α) : cs.limit.IsInfinite ↔ cs.Progressive := by
  constructor
  · intro hinf
    by_contra h
    obtain ⟨N, hN⟩ := eventually_const_of_not_progressive h
    have hlim : cs.Limit (.fin (cs.prefixAt N)) := ⟨N, hN⟩
    rw [limit_eq_iff.mpr hlim] at hinf
    exact hinf trivial
  · intro h
    obtain ⟨s, hs⟩ := exists_limit_inf h
    rw [limit_eq_iff.mpr hs]
    exact id

theorem isFinite_limit_iff (cs : Chunks α) : cs.limit.IsFinite ↔ ¬ cs.Progressive := by
  rw [← isInfinite_limit_iff, Word.IsInfinite, not_not]

/-! ## Rechunking -/

/-- Two chunk streams whose delivered prefixes are mutually cofinal have the same limit. -/
theorem limit_eq_of_cofinal {cs cs' : Chunks α}
    (h₁ : ∀ n, ∃ m, cs.prefixAt n <+: cs'.prefixAt m)
    (h₂ : ∀ m, ∃ n, cs'.prefixAt m <+: cs.prefixAt n) : cs.limit = cs'.limit := by
  symm
  apply limit_eq_iff.mpr
  have hl := limit_spec cs
  generalize cs.limit = t at hl
  cases t with
  | fin w =>
    obtain ⟨N, hN⟩ := hl
    obtain ⟨m₀, hm₀⟩ := h₁ N
    rw [hN N le_rfl] at hm₀
    refine ⟨m₀, fun m hm => ?_⟩
    have lower : w <+: cs'.prefixAt m := hm₀.trans (prefixAt_mono cs' hm)
    obtain ⟨n, hn⟩ := h₂ m
    have upper : cs'.prefixAt m <+: w := by
      have := hn.trans (prefixAt_mono cs (Nat.le_max_left n N))
      rwa [hN _ (Nat.le_max_right n N)] at this
    exact (lower.eq_of_length (Nat.le_antisymm lower.length_le upper.length_le)).symm
  | inf s =>
    obtain ⟨hp, hunb⟩ := hl
    refine ⟨fun m => ?_, fun k => ?_⟩
    · obtain ⟨n, hn⟩ := h₂ m
      exact hasPrefix_of_isPrefix (hp n) hn
    · obtain ⟨n, hn⟩ := hunb k
      obtain ⟨m, hm⟩ := h₁ n
      exact ⟨m, hn.trans hm.length_le⟩

/-! ## Embedding finite and infinite words as chunk streams -/

theorem prefixAt_ofList (cs : List (List α)) (n : ℕ) :
    (Chunks.ofList cs).prefixAt n = (cs.take n).flatten := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [prefixAt_succ, ih, List.take_add_one, List.flatten_append]
    show _ ++ cs.getD n [] = _
    rw [List.getD_eq_getElem?_getD]
    cases cs[n]? <;> simp

theorem limit_ofList (cs : List (List α)) : (Chunks.ofList cs).limit = .fin cs.flatten :=
  limit_eq_iff.mpr ⟨cs.length, fun n hn => by rw [prefixAt_ofList, List.take_of_length_le hn]⟩

theorem prefixAt_ofω (s : ωSequence α) (n : ℕ) : (Chunks.ofω s).prefixAt n = s.take n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [prefixAt_succ, ih, ωSequence.take_succ']; rfl

theorem limit_ofω (s : ωSequence α) : (Chunks.ofω s).limit = .inf s :=
  limit_eq_iff.mpr ⟨fun n => by
    show s.take ((Chunks.ofω s).prefixAt n).length = _
    rw [prefixAt_ofω, ωSequence.length_take],
    fun k => ⟨k, by rw [prefixAt_ofω, ωSequence.length_take]⟩⟩

/-- With all chunks nonempty, the limit is CSLib's `ωSequence.flatten`. -/
theorem limit_eq_flatten [Inhabited α] {cs : Chunks α} (h : ∀ k, cs k ≠ []) :
    cs.limit = .inf cs.flatten := by
  have hpos : ∀ k, 0 < (cs k).length := fun k => List.length_pos_iff.mpr (h k)
  have hprog : cs.Progressive := fun N => ⟨N, le_rfl, h N⟩
  refine limit_eq_iff.mpr ⟨fun n => ?_, unbounded_of_progressive hprog⟩
  show cs.flatten.take (cs.prefixAt n).length = cs.prefixAt n
  rw [Chunks.prefixAt, ωSequence.flatten_take hpos, ωSequence.length_take]

/-! ## Finite and infinite words -/

theorem isCompl_range :
    IsCompl (Set.range (Word.ofList : List α ↪ Word α)) (Set.range (Word.ofω : ωSequence α ↪ Word α)) := by
  constructor
  · rw [Set.disjoint_left]
    rintro _ ⟨w, rfl⟩ ⟨s, hs⟩
    cases hs
  · rw [codisjoint_iff, Set.top_eq_univ, Set.eq_univ_iff_forall]
    rintro (w | s)
    · exact Or.inl ⟨w, rfl⟩
    · exact Or.inr ⟨s, rfl⟩

/-- Infinite words cannot be injected into finite ones, already over `Bool` (Cantor). -/
theorem not_injective_ωSequence_list (f : ωSequence Bool → List Bool) : ¬ f.Injective := by
  classical
  intro hf
  let g : Set ℕ → ℕ := fun S => Encodable.encode (f ⟨fun n => decide (n ∈ S)⟩)
  apply Function.cantor_injective g
  intro S T h
  have := hf (Encodable.encode_injective h)
  ext n
  have := congrArg (fun x : ωSequence Bool => x.get n) this
  simpa using this

end Silmaril.Proofs.Semantics.Streams
