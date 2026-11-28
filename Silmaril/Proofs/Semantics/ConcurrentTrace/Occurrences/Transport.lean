module

public import Silmaril.Semantics.ConcurrentTrace.Occurrences.Defs
import Mathlib.Logic.Equiv.Basic

public section

namespace Silmaril.Proofs.Semantics.ConcurrentTrace.Occurrences

open Silmaril.Semantics.ConcurrentTrace

universe u v

variable {T : Type u} {E : Type v}

private def swapIndex (p i : Nat) : Nat :=
  Equiv.swap p (p + 1) i

private theorem swapIndex_lt {p i n : Nat} (hi : i < n) (hp : p + 1 < n) :
    swapIndex p i < n := by
  simp only [swapIndex, Equiv.swap_apply_def]
  split_ifs <;> omega

/-- The transposition on positions, across two words of the same length. -/
private def swapPositions {n m : Nat} (p : Nat) (hp : p + 1 < n) (hlen : n = m) :
    Fin n ≃ Fin m where
  toFun i := ⟨swapIndex p i, swapIndex_lt (hlen ▸ i.isLt) (hlen ▸ hp)⟩
  invFun j := ⟨swapIndex p j, swapIndex_lt (hlen.symm ▸ j.isLt) hp⟩
  left_inv i := Fin.ext (Equiv.swap_apply_self p (p + 1) i.val)
  right_inv j := Fin.ext (Equiv.swap_apply_self p (p + 1) j.val)

private theorem swapIndex_order {p i j : Nat}
    (hij : ¬ (i = p ∧ j = p + 1)) (hji : ¬ (i = p + 1 ∧ j = p)) :
    swapIndex p i < swapIndex p j ↔ i < j := by
  simp only [swapIndex, Equiv.swap_apply_def]
  split_ifs <;> omega

private abbrev swappedWord (pre post : Word T E) (a b : Letter T E) : Word T E :=
  pre ++ [a, b] ++ post

private def swapWordPositions (pre post : Word T E) (a b : Letter T E) :
    Fin (swappedWord pre post a b).length ≃ Fin (swappedWord pre post b a).length :=
  swapPositions pre.length (by simp [swappedWord]) (by simp [swappedWord])

private theorem label_at_first (pre post : Word T E) (a b : Letter T E)
    {i : Fin (swappedWord pre post a b).length} (hi : i.val = pre.length) :
    (swappedWord pre post a b)[i] = a := by
  simp [swappedWord, List.append_assoc, hi]

private theorem label_at_second (pre post : Word T E) (a b : Letter T E)
    {i : Fin (swappedWord pre post a b).length} (hi : i.val = pre.length + 1) :
    (swappedWord pre post a b)[i] = b := by
  simp [swappedWord, List.append_assoc, hi]

private theorem labels_swap (pre post : Word T E) (a b : Letter T E)
    (i : Fin (swappedWord pre post a b).length) :
    (swappedWord pre post b a)[swapWordPositions pre post a b i] =
      (swappedWord pre post a b)[i] := by
  by_cases hfirst : i.val = pre.length
  · rw [label_at_first pre post a b hfirst]
    apply label_at_second
    simp [swapWordPositions, swapPositions, swapIndex, hfirst]
  by_cases hsecond : i.val = pre.length + 1
  · rw [label_at_second pre post a b hsecond]
    apply label_at_first
    simp [swapWordPositions, swapPositions, swapIndex, hsecond]
  have hfixed : (swapWordPositions pre post a b i).val = i.val :=
    Equiv.swap_apply_of_ne_of_ne hfirst hsecond
  by_cases hpre : i.val < pre.length
  · simp [swappedWord, List.append_assoc, List.getElem_append_left hpre, hfixed]
  · have hpost : (pre ++ [a, b]).length ≤ i.val := by simp; omega
    have hpost' : (pre ++ [b, a]).length ≤ (swapWordPositions pre post a b i).val := by
      simpa [hfixed] using hpost
    change (pre ++ [b, a] ++ post)[(swapWordPositions pre post a b i).val] =
      (pre ++ [a, b] ++ post)[i.val]
    rw [List.getElem_append_right hpost, List.getElem_append_right hpost']
    simp [hfixed]

private theorem independent_symm {a b : Letter T E} (h : a.Independent b) : b.Independent a := by
  cases h with
  | events h => exact .events (Ne.symm h)
  | eventSync h => exact .syncEvent h
  | syncEvent h => exact .eventSync h

private theorem edges_swap (pre post : Word T E) {a b : Letter T E} (hab : a.Independent b)
    (i j : Fin (swappedWord pre post a b).length) :
    OccurrencePoset.Edge (swappedWord pre post b a)
        (swapWordPositions pre post a b i) (swapWordPositions pre post a b j) ↔
      OccurrencePoset.Edge (swappedWord pre post a b) i j := by
  simp only [OccurrencePoset.Edge, labels_swap]
  by_cases hij : i.val = pre.length ∧ j.val = pre.length + 1
  · rw [label_at_first pre post a b hij.1, label_at_second pre post a b hij.2]
    simp [hab]
  by_cases hji : i.val = pre.length + 1 ∧ j.val = pre.length
  · rw [label_at_second pre post a b hji.1, label_at_first pre post a b hji.2]
    simp [independent_symm hab]
  exact and_congr_left' (swapIndex_order hij hji)

private theorem causal_iff_of_edge_equiv {α β : Type*} {r : α → α → Prop} {s : β → β → Prop}
    (f : α ≃ β) (h : ∀ i j, s (f i) (f j) ↔ r i j) (i j : α) :
    Relation.TransGen s (f i) (f j) ↔ Relation.TransGen r i j := by
  have hinv (x y : β) : s x y → r (f.symm x) (f.symm y) := by
    simpa using (h (f.symm x) (f.symm y)).mp
  constructor
  · intro hs
    simpa only [Function.onFun, Equiv.symm_apply_apply] using Relation.TransGen.lift f.symm hinv _ _ hs
  · exact Relation.TransGen.lift f (fun i j => (h i j).mpr) i j

def swapIso (pre post : Word T E) {a b : Letter T E} (h : a.Independent b) :
    OccurrencePoset.Iso (OccurrencePoset.ofWord (pre ++ [a, b] ++ post))
      (OccurrencePoset.ofWord (pre ++ [b, a] ++ post)) where
  equiv := swapWordPositions pre post a b
  label_eq := labels_swap pre post a b
  before_iff := causal_iff_of_edge_equiv _ (edges_swap pre post h)

theorem swapIso_apply_val (pre post : Word T E) {a b : Letter T E} (h : a.Independent b)
    (i : Fin (OccurrencePoset.ofWord (pre ++ [a, b] ++ post)).size) :
    ((swapIso pre post h).equiv i).val =
      if i.val = pre.length then pre.length + 1
      else if i.val = pre.length + 1 then pre.length else i.val :=
  Equiv.swap_apply_def _ _ _

private theorem context_iso {x y : FreeMonoid (Letter T E)} (h : ConGen.Rel Swap x y)
    (pre post : Word T E) :
    Nonempty (OccurrencePoset.Iso (OccurrencePoset.ofWord (pre ++ x.toList ++ post))
      (OccurrencePoset.ofWord (pre ++ y.toList ++ post))) := by
  induction h generalizing pre post with
  | of _ _ h =>
    cases h with
    | pair h => exact ⟨swapIso pre post h⟩
  | refl => exact ⟨OccurrencePoset.Iso.refl _⟩
  | symm _ ih =>
    obtain ⟨f⟩ := ih pre post
    exact ⟨f.symm⟩
  | trans _ _ ih₁ ih₂ =>
    obtain ⟨f⟩ := ih₁ pre post
    obtain ⟨g⟩ := ih₂ pre post
    exact ⟨f.trans g⟩
  | @mul w x y z _ _ ih₁ ih₂ =>
    have h₁ := ih₁ pre (y.toList ++ post)
    have h₂ := ih₂ (pre ++ x.toList) post
    simp only [FreeMonoid.toList_mul, List.append_assoc] at h₁ h₂ ⊢
    obtain ⟨f⟩ := h₁
    obtain ⟨g⟩ := h₂
    exact ⟨f.trans g⟩

theorem equivalent_iso {x y : Word T E} (h : Equivalent x y) :
    Nonempty (OccurrencePoset.Iso (OccurrencePoset.ofWord x) (OccurrencePoset.ofWord y)) := by
  have h' : ConGen.Rel Swap (FreeMonoid.ofList x) (FreeMonoid.ofList y) := h
  simpa using context_iso h' [] []

end Silmaril.Proofs.Semantics.ConcurrentTrace.Occurrences
