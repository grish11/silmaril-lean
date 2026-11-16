module

public import Silmaril.Logic.Matching.FixedPoint.Simultaneous.Thms

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Matching.FixedPoint.Simultaneous.Examples
open CategoryTheory
open Algebraic.ManySorted (Signature)

inductive Operation : {n : Nat} → (Fin n → Bool) → Bool → Type
  | seed : Operation (n := 0) Fin.elim0 false
  | toLeft : Operation (fun _ : Fin 1 => true) false
  | toRight : Operation (fun _ : Fin 1 => false) true

def signature : Signature Bool := ⟨fun n inputs output => @Operation n inputs output⟩
def coordinates : Fin 2 → Bool := Fin.cases false (Fin.cases true Fin.elim0)

def «mutual» : System signature coordinates (fun i : Fin 0 => i.elim0)
    (fun i : Fin 0 => i.elim0) where
  body := Fin.cases
    (.disj (.app Operation.seed (fun i => i.elim0))
      (.app Operation.toLeft (fun _ => .setvar 1)))
    (Fin.cases (.app Operation.toRight (fun _ => .setvar 0)) (fun i => i.elim0))

/-- Both actual scalar native patterns arise from a genuinely two-sort block. -/
theorem mutual_correct (M : Model signature) :
    (fun i => (mutual.compile i).denote M (fun i => i.elim0) (fun i => i.elim0)) =
      mutual.denote M (fun i => i.elim0) (fun i => i.elim0) :=
  mutual.compile_correct M _ _

def unseeded : System signature coordinates (fun i : Fin 0 => i.elim0)
    (fun i : Fin 0 => i.elim0) where
  body := Fin.cases
    (.app Operation.toLeft (fun _ => .setvar 1))
    (Fin.cases (.app Operation.toRight (fun _ => .setvar 0)) (fun i => i.elim0))

theorem unseeded_operator_bot (M : Model signature) :
    unseeded.operator M (fun i => i.elim0) (fun i => i.elim0) ⊥ = ⊥ := by
  funext i
  refine Fin.cases ?_ (Fin.cases ?_ (fun j => j.elim0)) i
  · ext x
    change (∃ values, (∀ j : Fin 1, values j ∈ (∅ : Set (M.carrier true))) ∧
      x ∈ M.operation Operation.toLeft values) ↔ False
    constructor
    · rintro ⟨values, hv, _⟩; exact hv 0
    · exact False.elim
  · ext x
    change (∃ values, (∀ j : Fin 1, values j ∈ (∅ : Set (M.carrier false))) ∧
      x ∈ M.operation Operation.toRight values) ↔ False
    constructor
    · rintro ⟨values, hv, _⟩; exact hv 0
    · exact False.elim

/-- Native carriers remain the existing inhabited carriers, while both
unseeded generated subsets are genuinely empty. -/
theorem unseeded_empty (M : Model signature) :
    unseeded.denote M (fun i => i.elim0) (fun i => i.elim0) = ⊥ := by
  apply le_antisymm
  · exact (unseeded.operator M _ _).lfp_le (unseeded_operator_bot M).le
  · exact bot_le

/-- There is no least-fixed-point coordinate to choose for an empty family. -/
theorem empty_family {S : Type} {A : Signature S} {l k : Nat}
    {Q : Fin l → S} {Γ : Fin k → S}
    (s : System A (fun i : Fin 0 => i.elim0) Q Γ)
    (M : Model A) (v : ObjEnv A M Γ) (η : SetEnv A M Q) :
    (fun i => (s.compile i).denote M v η) = s.denote M v η :=
  s.compile_correct M v η

/-- The sort collapse is a real varying-sort map. Its operation category is
unrestricted, so the two original recursion coordinates remain distinct. -/
def collapsed : SortMaps.Signature :=
  ⟨Unit, ⟨fun _ _ _ => Unit⟩⟩

def collapse : (⟨Bool, signature⟩ : SortMaps.Signature) ⟶ collapsed :=
  ⟨fun _ => (), fun _ => ()⟩

def collapsedMutual := mutual.map collapse

theorem collapse_preserves_two_coordinates :
    (collapse.sorts ∘ coordinates) 0 = (collapse.sorts ∘ coordinates) 1 := rfl

theorem collapsed_mutual_correct (M : Model collapsed.symbols) :
    (fun i => (collapsedMutual.compile i).denote M
      (fun i => i.elim0) (fun i => i.elim0)) =
      collapsedMutual.denote M (fun i => i.elim0) (fun i => i.elim0) :=
  collapsedMutual.compile_correct M _ _

end Silmaril.Logic.Matching.FixedPoint.Simultaneous.Examples
