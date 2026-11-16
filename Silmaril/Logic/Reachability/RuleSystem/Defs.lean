module

public import Silmaril.Logic.Reachability.AllPath.Thms

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Reachability.RuleSystem

/-- A rule's variables belong to the rule, independently of a claim's captures. -/
structure Scheme (W : Type) where
  Parameters : Type
  lhs : Parameters → W → Prop
  rhs : Parameters → W → Prop

/-- Definition 3's induced transition: the same rule valuation binds both ends. -/
def Induced {W ι : Type} (rules : ι → Scheme W) (w v : W) : Prop :=
  ∃ i, ∃ a : (rules i).Parameters, (rules i).lhs a w ∧ (rules i).rhs a v

def WeaklyWellDefined {W ι : Type} (rules : ι → Scheme W) : Prop :=
  ∀ i a w, (rules i).lhs a w → ∃ v, (rules i).rhs a v

/-- Source coverage in the Step rule. No rule valuation is a claim valuation. -/
def Covers {W ι : Type} (rules : ι → Scheme W) (P : W → Prop) : Prop :=
  ∀ w, P w → ∃ i, ∃ a : (rules i).Parameters, (rules i).lhs a w

/-- Every rule instance must be accounted for, including overlapping competitors. -/
def SuccessorsIn {W ι : Type} (rules : ι → Scheme W) (P Q : W → Prop) : Prop :=
  ∀ i a w v, P w → (rules i).lhs a w → (rules i).rhs a v → Q v

/-- A finite cyclic proof graph. Each non-target node makes actual progress;
all generated successors reach the target or another node. -/
structure Certificate {W ι : Type} (rules : ι → Scheme W) (Q : W → Prop) (n : Nat) where
  node : Fin n → W → Prop
  cover : ∀ j, Covers rules (fun w => node j w ∧ ¬ Q w)
  successors : ∀ j, SuccessorsIn rules (fun w => node j w ∧ ¬ Q w)
    (fun v => Q v ∨ ∃ k, node k v)

/-- An intrinsically sorted matching rule interpreted in the original model. -/
def patternScheme {S : Type} {cfg : S} {A : Signature cfg} (M : Model cfg A)
    {n : Nat} {Γ : Fin n → S}
    (lhs rhs : Matching.FirstOrder.Pattern A.algebra Γ cfg) : Scheme (M.carrier cfg) where
  Parameters := (i : Fin n) → M.carrier (Γ i)
  lhs a w := w ∈ M.denote a lhs
  rhs a w := w ∈ M.denote a rhs

end Silmaril.Logic.Reachability.RuleSystem
