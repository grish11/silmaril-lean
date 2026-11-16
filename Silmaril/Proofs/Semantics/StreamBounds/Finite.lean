module

public import Silmaril.Semantics.StreamBounds.Defs
public import Silmaril.Semantics.Accept.Defs

/-! # Proofs: running bounds on finite words and completeness relative to a bound -/

@[expose] public section

namespace Silmaril.Proofs.Semantics.StreamBounds

open Silmaril.Streams Silmaril.Acceptor

universe u v w x

variable {α : Type u} {τ : Type v}

theorem mem_runBound_self {f : List α → ℕ} (w : List α) :
    w ∈ RunBound f (w.inits.map f).sum := by
  intro p hp
  exact List.le_sum_of_mem (List.mem_map.mpr ⟨p, List.mem_inits _ _ |>.mpr hp, rfl⟩)

theorem iUnion_runBound (f : List α → ℕ) : ⋃ n, RunBound f n = Set.univ :=
  Set.eq_univ_of_forall fun w => Set.mem_iUnion.mpr ⟨_, mem_runBound_self w⟩

theorem runBound_length (n : ℕ) : RunBound (List.length : List α → ℕ) n = {w | w.length ≤ n} := by
  ext w
  exact ⟨fun h => h w (List.prefix_refl w), fun h _ hp => hp.length_le.trans h⟩

theorem gap_append_singleton (isSep : α → Bool) (w : List α) (a : α) :
    gap isSep (w ++ [a]) = if isSep a then 0 else gap isSep w + 1 := by
  simp [gap, List.foldl_append]

theorem gap_le_length (isSep : α → Bool) (w : List α) : gap isSep w ≤ w.length := by
  induction w using List.reverseRecOn with
  | nil => simp [gap]
  | append_singleton w a ih =>
    rw [gap_append_singleton]; split <;> simp; omega

theorem depthStep_le (kind : τ → BracketKind) (d : ℕ) (t : τ) : depthStep kind d t ≤ d + 1 := by
  unfold depthStep; split <;> omega

theorem depth_append_singleton (kind : τ → BracketKind) (w : List τ) (t : τ) :
    depth kind (w ++ [t]) = depthStep kind (depth kind w) t := by
  simp [depth, List.foldl_append]

theorem depth_le_length (kind : τ → BracketKind) (w : List τ) : depth kind w ≤ w.length := by
  induction w using List.reverseRecOn with
  | nil => simp [depth]
  | append_singleton w a ih =>
    rw [depth_append_singleton]; have := depthStep_le kind (depth kind w) a; simp; omega

theorem runBound_mono_measure {f g : List α → ℕ} (h : ∀ w, f w ≤ g w) (n : ℕ) :
    RunBound g n ≤ RunBound f n :=
  fun _ hw p hp => (h p).trans (hw p hp)

theorem netDepth_append_singleton (kind : τ → BracketKind) (w : List τ) (t : τ) :
    netDepth kind (w ++ [t]) = netDepth kind w + bracketDelta kind t := by
  simp [netDepth]

/-- Without underflow, the truncated depth is the net depth. -/
theorem depth_eq_netDepth {kind : τ → BracketKind} {w : List τ}
    (h : ∀ p, p <+: w → 0 ≤ netDepth kind p) : (depth kind w : ℤ) = netDepth kind w := by
  induction w using List.reverseRecOn with
  | nil => simp [depth, netDepth]
  | append_singleton w a ih =>
    have ih := ih fun p hp => h p (hp.trans (List.prefix_append w [a]))
    have ha := h _ (List.prefix_refl _)
    rw [netDepth_append_singleton] at ha ⊢
    rw [depth_append_singleton]
    unfold depthStep bracketDelta at *
    split <;> simp_all; omega

/-! ## Completeness relative to a bound -/

variable {σ : Type w} {χ : Type x} [ChunkView χ α]

theorem correctFold_iff (A : Acceptor σ χ) (L : Language α) [DecidablePred (· ∈ L)] :
    A.CorrectFold L ↔ A.SoundFold L ∧ A.CompleteFoldOn L Set.univ := by
  constructor
  · intro h
    refine ⟨fun cs hy => ?_, fun cs hL _ => ?_⟩
    · rw [h cs] at hy; exact of_decide_eq_true hy
    · rw [h cs]; exact decide_eq_true hL
  · rintro ⟨hs, hc⟩ cs
    unfold member
    by_cases hL : cs.flatMap ChunkView.toList ∈ L
    · rw [decide_eq_true hL]; exact hc cs hL trivial
    · rw [decide_eq_false hL]
      cases hq : (A.query (cs.foldl A.process A.init)).1
      · rfl
      · exact absurd (hs cs hq) hL

theorem completeFoldOn_univ_of_iUnion {A : Acceptor σ χ} {L : Language α} {ι : Sort*}
    {B : ι → Language α} (hB : ⋃ i, B i = Set.univ) (h : ∀ i, A.CompleteFoldOn L (B i)) :
    A.CompleteFoldOn L Set.univ := by
  intro cs hL _
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hB ▸ Set.mem_univ (cs.flatMap ChunkView.toList))
  exact h i cs hL hi

theorem foldl_append_toList (cs : List χ) (acc : List α) :
    cs.foldl (fun w c => w ++ ChunkView.toList c) acc = acc ++ cs.flatMap ChunkView.toList := by
  induction cs generalizing acc with
  | nil => simp
  | cons c cs ih => simp [ih]

theorem boundedReference_answer (L B : Language α) [DecidablePred (· ∈ L)]
    [DecidablePred (· ∈ B)] (cs : List χ) :
    ((boundedReference (χ := χ) L B).query
      (cs.foldl (boundedReference (χ := χ) L B).process (boundedReference (χ := χ) L B).init)).1 =
      (member L (cs.flatMap ChunkView.toList) && member B (cs.flatMap ChunkView.toList)) := by
  simp only [boundedReference]
  rw [foldl_append_toList]; simp

theorem boundedReference_correctFold (L B : Language α) [DecidablePred (· ∈ L)]
    [DecidablePred (· ∈ B)] : (boundedReference (χ := χ) L B).CorrectFold (L ⊓ B) := by
  intro cs
  rw [boundedReference_answer]
  simp [member, Language.mem_inf]

theorem boundedReference_soundFold (L B : Language α) [DecidablePred (· ∈ L)]
    [DecidablePred (· ∈ B)] : (boundedReference (χ := χ) L B).SoundFold L := by
  intro cs h
  rw [boundedReference_answer] at h
  simp only [member, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

theorem boundedReference_completeFoldOn (L B : Language α) [DecidablePred (· ∈ L)]
    [DecidablePred (· ∈ B)] : (boundedReference (χ := χ) L B).CompleteFoldOn L B := by
  intro cs hL hB
  rw [boundedReference_answer]
  simp [member, hL, hB]

theorem boundedReference_not_completeFoldOn_univ {L B : Language α} [DecidablePred (· ∈ L)]
    [DecidablePred (· ∈ B)] {w : List α} (hL : w ∈ L) (hB : w ∉ B) :
    ¬ (boundedReference (χ := List α) L B).CompleteFoldOn L Set.univ := by
  intro h
  have := h [w] (by simpa [ChunkView.toList] using hL) trivial
  rw [boundedReference_answer] at this
  simp [member, ChunkView.toList, hB] at this

end Silmaril.Proofs.Semantics.StreamBounds
