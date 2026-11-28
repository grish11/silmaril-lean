module

public import Silmaril.Semantics.ConcurrentTrace.PartialSequence.Defs

public section

namespace Silmaril.Proofs.Semantics.ConcurrentTrace

open Silmaril.Semantics.ConcurrentTrace

variable {E R F S : Type*}

theorem prefix_take (s : PartialSequence E R) {m n : Nat} (h : m ≤ n) :
    (s.cut n).take m = s.cut m := by
  cases s with
  | pending w | done w _ => simp [PartialSequence.cut, List.take_take, Nat.min_eq_left h]
  | infinite events =>
    apply List.ext_getElem
    · simp [PartialSequence.cut, Nat.min_eq_left h]
    · intro i hi hj
      rw [List.getElem_take]
      simp [PartialSequence.cut]

theorem length_prefix_le (s : PartialSequence E R) (n : Nat) : (s.cut n).length ≤ n := by
  cases s <;> simp [PartialSequence.cut]

theorem hasPrefix_iff (s : PartialSequence E R) (w : List E) :
    s.HasPrefix w ↔ ∃ n, w <+: s.cut n := by
  constructor
  · intro h
    refine ⟨w.length, ?_⟩
    rw [show s.cut w.length = w from h]
    exact List.prefix_refl _
  · rintro ⟨n, h⟩
    unfold PartialSequence.HasPrefix
    rw [← prefix_take s (h.length_le.trans (length_prefix_le s n))]
    exact (List.prefix_iff_eq_take.mp h).symm

theorem eq_of_prefix_eq (s t : PartialSequence E R) (h : ∀ n, s.cut n = t.cut n)
    (hr : s.completion = t.completion) : s = t := by
  have finiteWord {w v : List E} (hv : ∀ n, w.take n = v.take n) : w = v := by
    simpa [List.take_of_length_le, le_max_left, le_max_right] using
      hv (max w.length v.length)
  have finiteInfinite (w : List E) (f : Nat → E)
      (hf : ∀ n, w.take n = List.ofFn (fun i : Fin n => f i)) : False := by
    have impossible := congrArg List.length (hf (w.length + 1))
    simp at impossible
  cases s with
  | pending w =>
    cases t with
    | pending v => exact congrArg PartialSequence.pending (finiteWord h)
    | done v r => cases hr
    | infinite f => exact (finiteInfinite w f h).elim
  | done w r =>
    cases t with
    | pending v | infinite _ => cases hr
    | done v r' =>
      have he : r = r' := Option.some.inj hr
      exact congrArg₂ PartialSequence.done (finiteWord h) he
  | infinite f =>
    cases t with
    | pending w => exact (finiteInfinite w f (fun n => (h n).symm)).elim
    | done w r => cases hr
    | infinite g =>
      refine congrArg PartialSequence.infinite (funext fun n => ?_)
      have atIndex := congrArg (fun w : List E => w[n]?) (h (n + 1))
      simpa only [PartialSequence.cut, List.getElem?_ofFn, dite_eq_left (Nat.lt_succ_self n),
        Option.some.injEq] using atIndex

theorem prefix_eq_of_rawPrefixes (s t : PartialSequence E R)
    (h : ∀ w, s.HasPrefix w ↔ t.HasPrefix w) (n : Nat) : s.cut n = t.cut n := by
  have below {s t : PartialSequence E R} (hs : ∀ w, s.HasPrefix w → t.HasPrefix w) :
      s.cut n <+: t.cut n := by
    have present : s.HasPrefix (s.cut n) :=
      (hasPrefix_iff s _).2 ⟨n, List.prefix_refl _⟩
    rw [← show t.cut (s.cut n).length = s.cut n from hs _ present,
      ← prefix_take t (length_prefix_le s n)]
    exact List.take_prefix _ _
  exact (below fun w => (h w).1).eq_of_length_le (below fun w => (h w).2).length_le

theorem prefix_map (s : PartialSequence E R) (f : E → F) (g : R → S) (n : Nat) :
    (s.map f g).cut n = (s.cut n).map f := by
  cases s <;> simp [PartialSequence.map, PartialSequence.cut, List.map_ofFn,
    Function.comp_def]

theorem completion_bounded (s : PartialSequence E R) (h : s.completion.isSome) :
    ∃ n, (s.cut n).length < n := by
  cases s with
  | done w r => exact ⟨w.length + 1, by simp [PartialSequence.cut]⟩
  | pending w | infinite _ => cases h

theorem realize_prefixes (s : PrefixSequence E R) :
    ∃ t : PartialSequence E R, (∀ n, t.cut n = s.cut n) ∧ t.completion = s.completion := by
  classical
  by_cases finite : ∃ n, (s.cut n).length < n
  · obtain ⟨bound, short⟩ := finite
    refine ⟨PartialSequence.finite (s.cut bound) s.completion, ?_, ?_⟩
    · intro n
      have cutFinite : (PartialSequence.finite (s.cut bound) s.completion).cut n =
          (s.cut bound).take n := by cases s.completion <;> rfl
      rw [cutFinite]
      rcases le_total n bound with h | h
      · exact s.take_eq h
      · have eqLen := congrArg List.length (s.take_eq h)
        rw [List.length_take] at eqLen
        have le : (s.cut n).length ≤ bound := by omega
        have same : s.cut n = s.cut bound := (List.take_of_length_le le).symm.trans (s.take_eq h)
        rw [same, List.take_of_length_le (Nat.le_trans (s.length_le bound) h)]
    · cases s.completion <;> rfl
  · have full (n : Nat) : (s.cut n).length = n :=
      Nat.le_antisymm (s.length_le n) (Nat.le_of_not_gt fun h => finite ⟨n, h⟩)
    have noReturn : s.completion = none := by
      cases h : s.completion with
      | none => rfl
      | some r => exact (finite (s.completion_bounded (by simp [h]))).elim
    let events (i : Nat) : E := (s.cut (i + 1))[i]'(by rw [full]; exact Nat.lt_succ_self _)
    refine ⟨.infinite events, fun n => ?_, noReturn.symm⟩
    apply List.ext_getElem
    · simp [PartialSequence.cut, full]
    · intro i hi hj
      have hle : i + 1 ≤ n := Nat.succ_le_of_lt ((full n) ▸ hj)
      have eq := congrArg (fun w : List E => w[i]?) (s.take_eq hle)
      have get : (s.cut n)[i]? = (s.cut (i + 1))[i]? := by
        simpa only [List.getElem?_take, ite_eq_left (Nat.lt_succ_self i)] using eq
      simp only [PartialSequence.cut, List.getElem_ofFn]
      have hh : i < (s.cut (i + 1)).length := by rw [full]; exact Nat.lt_succ_self _
      simpa only [events, List.getElem?_eq_getElem hj, List.getElem?_eq_getElem hh,
        Option.some.injEq] using get.symm

end Silmaril.Proofs.Semantics.ConcurrentTrace
