module

public import Silmaril.Wasm.Logic.Separation.Wasm.Thms

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Separation.Examples
open Silmaril.Wasm.Logic.Sep

abbrev atomSignature : Signature := ⟨Unit⟩
abbrev empIntroduction : Sentence atomSignature :=
  ⟨.base (.atom ()), .base (.sep .emp (.atom ()))⟩

theorem emp_introduction_valid (M : Model atomSignature) : empIntroduction.Satisfies M := by
  intro h hp
  change h ∈ M.resource.sep {M.resource.unit} (M.atom ())
  rw [Resource.emp_sep]
  exact hp

/-- An actual unrestricted matching model with a false emp interpretation. -/
abbrev badMatching : Matching.FirstOrder.Model (matchingSignature atomSignature) where
  carrier _ := Unit
  nonempty _ := inferInstance
  operation op _ := match op with
    | .emp => ∅
    | _ => {_h | True}

theorem emp_introduction_unrestricted_invalid : ¬ (encode empIntroduction).Satisfies badMatching := by
  intro h
  have hp := h (fun i => i.elim0) (fun i => i.elim0) ()
  change (¬ () ∈ badMatching.denote (fun i : Fin 0 => i.elim0) (compileBase (.atom ()))) ∨
    () ∈ badMatching.denote (fun i : Fin 0 => i.elim0) (compileBase (.sep .emp (.atom ()))) at hp
  cases hp with
  | inl hn => exact hn ⟨(fun i => i.elim0), (fun i => i.elim0), trivial⟩
  | inr hp =>
      obtain ⟨args, ha, _⟩ := hp
      obtain ⟨_, _, he⟩ := ha 0
      exact he

theorem negative_recursion_not_monotone : ¬ Monotone (fun X : Set Unit => Xᶜ) := by
  intro h
  have bad : (Set.univ : Set Unit) ⊆ ∅ := by
    simpa only [Set.compl_empty, Set.compl_univ] using
      h (show (∅ : Set Unit) ⊆ Set.univ from Set.empty_subset _)
  exact bad (Set.mem_univ ())

theorem mu_self_is_empty {A : Signature} (M : Model A) :
    (.mu (.var 0) : Pattern A 0).denote M (fun i => i.elim0) = ∅ := by
  apply Set.Subset.antisymm
  · exact Pattern.mu_induction M (.var 0) _ ∅ (fun _ h => h)
  · exact Set.empty_subset _

theorem same_cell_conjunction (l : Loc) (c : Cell) :
    pointsTo l c (Heap.single l c) ∧ pointsTo l c (Heap.single l c) := ⟨rfl,rfl⟩

theorem same_cell_cannot_separate (l : Loc) (c : Cell) (h : Heap) : ¬ (pointsTo l c ∗ pointsTo l c) h := by
  rintro ⟨a,b,hd,_,ha,hb⟩
  change a = Heap.single l c at ha
  change b = Heap.single l c at hb
  have bad := hd l
  rw [ha, hb] at bad
  simp [Heap.single] at bad

private theorem single_disjoint {l k : Loc} (hne : l ≠ k) (c d : Cell) :
    Heap.Disj (Heap.single l c) (Heap.single k d) := by
  intro x
  by_cases hx : x = l
  · exact Or.inr (by simp [Heap.single, hx, hne])
  · exact Or.inl (by simp [Heap.single, hx])

theorem two_cells_are_recursive (c d : Cell) :
    Wasm.finiteAssn ((Heap.single (.global 0) c).union (Heap.single (.global 1) d)) :=
  by
    apply Wasm.finite_cell _ _ (single_disjoint (by intro h; cases h) _ _)
    simpa only [Heap.union_empty] using
      Wasm.finite_cell (.global 1) d (Heap.disj_empty _) Wasm.finite_empty

/-- info: 'Silmaril.Logic.Separation.Resource.residuation' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Logic.Separation.Resource.residuation

/-- info: 'Silmaril.Logic.Separation.Pattern.mu_induction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Logic.Separation.Pattern.mu_induction

/-- info: 'Silmaril.Logic.Separation.baseToRecursive_modelExpansive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Logic.Separation.baseToRecursive_modelExpansive

/-- info: 'Silmaril.Logic.Separation.compilePattern_denote' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Logic.Separation.compilePattern_denote

/-- info: 'Silmaril.Logic.Separation.encode_satisfaction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Logic.Separation.encode_satisfaction

/-- info: 'Silmaril.Logic.Separation.toCanonicalMatching_modelExpansive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Logic.Separation.toCanonicalMatching_modelExpansive

/-- info: 'Silmaril.Logic.Separation.Wasm.finite_iff_inductive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Logic.Separation.Wasm.finite_iff_inductive

/-- info: 'Silmaril.Logic.Separation.Wasm.structGet_preserves_recursive_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Logic.Separation.Wasm.structGet_preserves_recursive_tail

end Silmaril.Logic.Separation.Examples
