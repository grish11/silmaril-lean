module

public import Silmaril.Games.Abstract.FullFun.Defs
public import Silmaril.Games.Abstract.HostRunInf.Thms
import Silmaril.Proofs.Games.Abstract.FullFun.Basic

/-!
# Full observations: copairing and the fixpoint law for iteration (proofs)

* `case_pure_map`: the copairing of the two injections is the identity;
* `streamConcat_cons`, `streamConcat_tail`: a concatenated stream with one more segment in
  front, and with its first segment split off;
* `iter_unfold_inf`: the productive runs of `iter F` are those of `seq F (case pure (iter F))`.
  A finite continuing chain followed by a productive run is either empty (a productive run of
  the first iteration) or a first continuing iteration followed by a shorter chain, and an
  infinite continuing chain is its first iteration followed by the shifted chain.
-/

@[expose] public section

namespace Silmaril.Proofs.Games.Abstract.FullFun

open Silmaril.Games Silmaril.Games.Abstract

universe u

variable {E : Sig.{u}} {S A B C : Type u}

/-- The copairing of the injections is the identity. -/
theorem case_pure_map :
    FullFun.case (FullFun.pure.map Sum.inl) (FullFun.pure.map Sum.inr) =
      (FullFun.pure : FullFun E S (A ⊕ B) (A ⊕ B)) := by
  refine Prod.ext ?_ ?_
  · funext s x
    cases x <;> simp [FullFun.case, AFun.case, FullFun.map, FullFun.pure, FullFun.endMap]
  · funext s x
    cases x <;> rfl

theorem flatMap_range_succ {α : Type u} (l : Nat → List α) (n : Nat) :
    (List.range (n + 1)).flatMap l = l 0 ++ (List.range n).flatMap fun i => l (i + 1) := by
  rw [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]

theorem streamPrefix_append {α : Type u} {c L : List α} {ω : Nat → α}
    (h : Shape.StreamPrefix L ω) : Shape.StreamPrefix (c ++ L) (c ++ₛ ω) := by
  intro i hi
  by_cases hc : i < c.length
  · rw [append_get_lt c ω hc, List.getElem_append_left hc]
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_lt hc)
    rw [append_get_ge, List.getElem_append_right (by omega)]
    simp only [Nat.add_sub_cancel_left]
    exact h j (by simp only [List.length_append] at hi; omega)

/-- A concatenated stream with one more segment in front. -/
theorem streamConcat_cons {α : Type u} {l : Nat → List α} {ω : Nat → α}
    (h : Shape.StreamConcat (fun n => l (n + 1)) ω) : Shape.StreamConcat l (l 0 ++ₛ ω) := by
  refine ⟨fun n => ?_, fun N => ?_⟩
  · cases n with
    | zero => intro i hi; simp at hi
    | succ n => rw [flatMap_range_succ]; exact streamPrefix_append (h.1 n)
  · obtain ⟨n, hn⟩ := h.2 N
    exact ⟨n + 1, by rw [flatMap_range_succ, List.length_append]; omega⟩

/-- A concatenated stream is its first segment in front of the concatenation of the rest. -/
theorem streamConcat_tail {α : Type u} {l : Nat → List α} {ω : Nat → α}
    (h : Shape.StreamConcat l ω) :
    ω = l 0 ++ₛ (fun i => ω ((l 0).length + i)) ∧
      Shape.StreamConcat (fun n => l (n + 1)) (fun i => ω ((l 0).length + i)) := by
  obtain ⟨hp, hu⟩ := h
  have hp' : ∀ n, Shape.StreamPrefix (l 0 ++ (List.range n).flatMap fun i => l (i + 1)) ω :=
    fun n => by rw [← flatMap_range_succ]; exact hp (n + 1)
  refine ⟨?_, fun n i hi => ?_, fun N => ?_⟩
  · funext i
    by_cases hc : i < (l 0).length
    · exact ((hp' 0 i (by simp only [List.length_append]; omega)).trans
        (List.getElem_append_left hc)).trans (append_get_lt _ _ hc).symm
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_lt hc)
      exact (append_get_ge (l 0) (fun i => ω ((l 0).length + i)) j).symm
  · have := hp' n ((l 0).length + i) (by simp only [List.length_append]; omega)
    rw [List.getElem_append_right (by omega)] at this
    simpa only [Nat.add_sub_cancel_left] using this
  · obtain ⟨n, hn⟩ := hu (N + (l 0).length)
    cases n with
    | zero => exact ⟨0, by simp at hn; omega⟩
    | succ n => exact ⟨n, by rw [flatMap_range_succ, List.length_append] at hn; omega⟩

/-- **The fixpoint law for iteration**, productive runs. -/
theorem iter_unfold_inf (F : FullFun E S A (B ⊕ A)) :
    (FullFun.iter F).2 = (FullFun.seq F (FullFun.case FullFun.pure (FullFun.iter F))).2 := by
  funext s a
  ext ω
  constructor
  · rintro (⟨c, s', a', ω', hc, hf, rfl⟩ | ⟨σ, l, h0, hσ, hl⟩)
    · cases hc with
      | refl => exact .inl hf
      | step hm hc =>
        exact .inr ⟨_, _, _, _, hm, .inl ⟨_, _, _, ω', hc, hf, rfl⟩,
          Stream'.append_append_stream _ _ _⟩
    · obtain ⟨heq, hl'⟩ := streamConcat_tail hl
      have h1 := hσ 0
      rw [h0] at h1
      exact .inr ⟨l 0, _, _, _, h1,
        .inr ⟨fun n => σ (n + 1), fun n => l (n + 1), rfl, fun n => hσ (n + 1), hl'⟩, heq⟩
  · rintro (hf | ⟨c, b | a₁, s₁, ω', hm, hω', rfl⟩)
    · exact .inl ⟨[], s, a, ω, .refl, hf, rfl⟩
    · exact hω'.elim
    · rcases hω' with ⟨c', s', a', ω'', hc, hf, rfl⟩ | ⟨σ, l, h0, hσ, hl⟩
      · exact .inl ⟨c ++ c', s', a', ω'', .step hm hc, hf,
          (Stream'.append_append_stream _ _ _).symm⟩
      · refine .inr ⟨fun n => match n with | 0 => (s, a) | n + 1 => σ n,
          fun n => match n with | 0 => c | n + 1 => l n, rfl, fun n => ?_, streamConcat_cons hl⟩
        cases n with
        | zero => show (c, End.ret (.inr (σ 0).2) (σ 0).1) ∈ F.1 s a; rw [h0]; exact hm
        | succ n => exact hσ n

end Silmaril.Proofs.Games.Abstract.FullFun
