module

public import Silmaril.Logic.Matching.GeneralFixedPoint.Variables.Algebraic

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Silmaril.Logic.Matching.GeneralFixedPoint.VariableExamples
open Algebraic.ManySorted (Signature)

abbrev signature : Signature Unit := ⟨fun _ _ _ => Empty⟩
abbrev context (n : Nat) : Fin n → Unit := fun _ => ()

/-- Both free namespaces occur inside an element binder and two set binders.
The free set occurs with both polarities; bound variables remain positive. -/
def mixed : Pattern signature (context 1) (context 1) () :=
  .ex () (.mu (P' := context 2) (.nu (P' := context 3) (.conj (.setvar 2)
    (.conj (.neg (.setvar 2)) (.base (.var 1))))))

/-- Replacements mention both namespaces; negation is allowed in a free set
replacement. Shifting prevents these free indices from becoming binder indices. -/
def replacement : Pattern signature (context 1) (context 1) () :=
  .conj (.neg (.setvar 0)) (.base (.var 0))

theorem mixed_admissible : mixed.admissible = true := rfl

theorem mixed_substitution_admissible :
    (mixed.substitute (fun _ => replacement) (fun _ => replacement)).admissible = true :=
  mixed.admissible_substitute _ _ mixed_admissible (fun _ => rfl) (fun _ => rfl)

theorem mixed_substitution_denote (M : Model signature)
    (v : ObjEnv signature M (context 1)) (η : SetEnv signature M (context 1)) :
    (mixed.substituteSets (fun _ => replacement)).denote M v η =
      mixed.denote M v (fun _ => replacement.denote M v η) :=
  mixed.denote_substituteSets M _ v η

/-- The free element in the replacement is still index 1 beneath ∃. -/
theorem object_capture_control :
    ((Pattern.ex () (.setvar 0) : Pattern signature (context 1) (context 1) ()).substituteSets (Q := context 1) (fun _ => .base (.var 0))) = .ex () (.base (.var 1)) := rfl

/-- A free negative set replacement remains free beneath μ. Capturing it
would instead create the invalid body `not X`. -/
theorem set_capture_control :
    ((Pattern.mu (P' := context 2) (.setvar 1) : Pattern signature (context 1) (context 1) ()).substituteSets (fun _ => .neg (.setvar 0))) = Pattern.mu (P' := context 2) (.neg (.setvar 1)) := rfl

/-- Element replacements also shift their free *set* indices beneath μ. -/
theorem cross_namespace_capture_control :
    ((Pattern.mu (P' := context 2) (.base (.var 0)) : Pattern signature (context 1) (context 1) ()).substituteObjects (Δ := context 1) (fun _ => .neg (.setvar 0))) = Pattern.mu (P' := context 2) (.neg (.setvar 1)) := rfl

abbrev constantSignature : Signature Unit := ⟨fun _ _ _ => Unit⟩
abbrev constantAlgebra : Algebraic.ManySorted.Model constantSignature where
  carrier _ := Nat
  operation _ _ := 7

def seven : Algebraic.ManySorted.Term constantSignature (context 1) () :=
  .app (n := 0) (inputs := context 0) () (fun i => i.elim0)

/-- An actual nullary operation term discharges functionalness by its model
interpretation. The surrounding pattern may contain any μ/ν/element binders. -/
theorem constant_term_client
    (p : Pattern constantSignature (context 1) (context 1) ())
    (σ : ∀ _ : Fin 1, Pattern constantSignature (context 1) (context 1) ())
    (v : Fin 1 → Nat) (η : Fin 1 → Set Nat) :
    (p.substitute σ (fun _ => .base (FirstOrder.Pattern.ofTerm seven))).denote
        (FirstOrder.Model.ofAlgebra constantAlgebra (fun _ => ⟨0⟩)) v η =
      p.denote (FirstOrder.Model.ofAlgebra constantAlgebra (fun _ => ⟨0⟩))
        (fun _ => (7 : Nat)) (fun i => (σ i).denote
          (FirstOrder.Model.ofAlgebra constantAlgebra (fun _ => ⟨0⟩)) v η) :=
  p.denote_substitute_terms constantAlgebra (fun _ => ⟨0⟩) σ (fun _ => seven) v η

abbrev boolModel : Model signature where
  carrier _ := Bool
  nonempty _ := ⟨false⟩
  operation op := nomatch op

/-- Both recursion coordinates occur positively. Its actual fixed point is
`{x} ∩ Y`; choosing x in Y gives a nonempty result. -/
def anchored : Pattern signature (context 1) (context 1) () :=
  .mu (P' := context 2) (.disj
    (.conj (.base (.var 0)) (.setvar 1))
    (.conj (.setvar 0) (.nu (P' := context 3) (.conj (.setvar 0) (.setvar 2)))))

theorem anchored_admissible : anchored.admissible = true := rfl

private theorem greatest_inter (Y : Set Bool) : sSup {Z : Set Bool | Z ⊆ Z ∩ Y} = Y := by
  apply le_antisymm
  · apply sSup_le
    intro Z hZ x hx
    exact (hZ hx).2
  · apply le_sSup
    intro x hx
    exact ⟨hx, hx⟩

theorem anchored_denote (v : ObjEnv signature boolModel (context 1))
    (η : SetEnv signature boolModel (context 1)) :
    anchored.denote boolModel v η = {v 0} ∩ η 0 := by
  change sInf {X : Set Bool |
    (({v 0} ∩ η 0)ᶜ ∩ (X ∩ sSup {Z : Set Bool | Z ⊆ Z ∩ η 0})ᶜ)ᶜ ⊆ X} = _
  rw [greatest_inter]
  have boolean (A B : Set Bool) : (Aᶜ ∩ Bᶜ)ᶜ = A ∪ B := by
    ext x
    simp
  simp only [boolean]
  apply le_antisymm
  · apply sInf_le
    intro x hx
    rcases hx with hx | hx
    · exact hx
    · exact hx.1
  · apply le_sInf
    intro X hX x hx
    exact hX (Or.inl hx)

/-- The element replacement `not x` at x=false is the actual singleton {true}.
The set replacement `not Y` at Y=∅ is the whole carrier. Both substitutions
run simultaneously through the genuinely used μ/ν coordinates. -/
theorem anchored_simultaneous_nonempty :
    (anchored.substitute (Q := context 1) (Δ := context 1)
      (fun _ => .neg (.setvar 0))
      (fun _ => .neg (.base (.var 0)))).denote
        boolModel (fun _ => false) (fun _ => ∅) = {true} := by
  have single : ∀ _ : Fin 1,
      (Pattern.neg (.base (.var 0)) : Pattern signature (context 1) (context 1) ()).denote
        boolModel (fun _ => false) (fun _ => ∅) = {true} := by
    intro i
    ext x
    cases x <;> simp [Pattern.denote, FirstOrder.Model.denote]
  rw [anchored.denote_substitute boolModel _ _ (fun _ => false) (fun _ => ∅)
    (fun _ => true) single, anchored_denote]
  ext x
  simp [Pattern.denote]

def top : Pattern signature (context 0) (context 1) () :=
  .neg (.conj (.base (.var 0)) (.neg (.base (.var 0))))

theorem top_denote (v : ObjEnv signature boolModel (context 1))
    (η : SetEnv signature boolModel (context 0)) : top.denote boolModel v η = Set.univ := by
  ext x
  simp [top, Pattern.denote]

/-- An arbitrary set replacement cannot act as an element valuation: this
replacement denotes both booleans, while any element variable denotes one. -/
theorem arbitrary_element_substitution_fails (w : Bool) :
    ((Pattern.base (FirstOrder.Pattern.var (A := signature) (Γ := context 1) 0) :
        Pattern signature (context 0) (context 1) ()).substituteObjects (fun _ => top)).denote
        boolModel (fun _ => false) (fun i => i.elim0) ≠ {w} := by
  change top.denote boolModel _ _ ≠ {w}
  rw [top_denote]
  intro h
  have member : (!w) ∈ ({w} : Set Bool) := h ▸ Set.mem_univ (!w)
  cases w <;> cases member

end Silmaril.Logic.Matching.GeneralFixedPoint.VariableExamples
