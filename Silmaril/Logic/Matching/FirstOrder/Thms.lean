module

public import Silmaril.Logic.Matching.FirstOrder.Defs

@[expose] public section
namespace Silmaril.Logic.Matching.FirstOrder
open Algebraic.ManySorted (Signature)
variable {S : Type} {A : Signature S} {k : Nat} {Γ : Fin k → S} {s : S}

/-- Source-derived truth pattern, expressed using existential binding. -/
def Pattern.top : Pattern A Γ s := .ex s (.var 0)
def Pattern.bottom : Pattern A Γ s := .neg Pattern.top

theorem Model.denote_top (M : Model A) (v : (i : Fin k) → M.carrier (Γ i)) :
    M.denote v (Pattern.top (s := s)) = Set.univ := by
  ext result
  change (∃ value : M.carrier s, result = value) ↔ True
  exact ⟨fun _ => trivial, fun _ => ⟨result, rfl⟩⟩

theorem Model.denote_bottom (M : Model A) (v : (i : Fin k) → M.carrier (Γ i)) :
    M.denote v (Pattern.bottom (s := s)) = ∅ := by
  change (M.denote v Pattern.top)ᶜ = ∅
  rw [M.denote_top, Set.compl_univ]

/-- A constant pattern denotes its full interpretation, including multiple results. -/
theorem Model.denote_nullary (M : Model A) (v : (i : Fin k) → M.carrier (Γ i))
    (op : A.operations 0 Fin.elim0 s) :
    M.denote v (.app op (fun i => nomatch i)) =
      M.operation op (fun i => nomatch i) := by
  ext result
  constructor
  · rintro ⟨values, _, member⟩
    have same : values = (fun i => nomatch i) := by funext i; exact Fin.elim0 i
    simpa only [same] using member
  · intro member
    exact ⟨(fun i => nomatch i), (fun i => nomatch i), member⟩

/-- Pattern inclusion in a fixed model, quantified over valuations. -/
def Model.Entails (M : Model A) (p q : Pattern A Γ s) : Prop :=
  ∀ v : (i : Fin k) → M.carrier (Γ i), M.denote v p ⊆ M.denote v q

theorem Model.entails_refl (M : Model A) (p : Pattern A Γ s) : M.Entails p p :=
  fun _ _ member => member

theorem Model.entails_trans (M : Model A) {p q r : Pattern A Γ s}
    (hpq : M.Entails p q) (hqr : M.Entails q r) : M.Entails p r :=
  fun v _ member => hqr v (hpq v member)
end Silmaril.Logic.Matching.FirstOrder
