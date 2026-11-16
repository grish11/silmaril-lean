module

public import Silmaril.Logic.Temporal.CTLStar.NNF.Thms
public import Silmaril.Logic.Temporal.CTLStar.Terminal.Examples

@[expose] public section
namespace Silmaril.Logic.Temporal.CTLStar.NNF.Examples
open Terminal.Examples

def word {S : Signature} (M : Model S) (path : Path M.toModal.accessible) :
    Nat → StateFormula S → Prop := fun t a => a.Holds M (path.state t)

/-- Normalizing ¬X true keeps the weak-next endpoint case. -/
theorem neg_next_syntax :
    normalize false (.neg (.next (PathFormula.top : PathFormula sig))) =
      Formula.weakNext (.neg StateFormula.top) := rfl

theorem singleton_normalized_neg_next :
    (normalize false (.neg (.next (PathFormula.top : PathFormula sig)))).Holds
      singletonPath.last (word singletonModel singletonPath) 0 := by
  apply (normalize_holds singletonModel singletonPath _ false 0 singletonPath.valid_zero).mpr
  exact singleton_not_next

/-- Reusing infinite NNF's strong-next dual would fail this endpoint control. -/
theorem singleton_wrong_strong_next_dual :
    ¬ (Formula.strongNext (.neg StateFormula.top)).Holds singletonPath.last
      (word singletonModel singletonPath) 0 :=
  Formula.strongNext_at_last _ _ 0

theorem singleton_normalized_postponement_fails :
    ¬ (normalize false (.until .top (.state .bot : PathFormula sig))).Holds
      singletonPath.last (word singletonModel singletonPath) 0 := by
  unfold word
  rw [normalize_holds singletonModel singletonPath _ false 0 singletonPath.valid_zero]
  exact singleton_until_postponement_fails

theorem singleton_release_finishes :
    (Formula.release .bot .top : Formula (StateFormula sig)).Holds singletonPath.last
      (word singletonModel singletonPath) 0 :=
  (Formula.release_at_last _ _ _ 0).mpr trivial

/-- The same normalization treats both actual positions of a one-edge path correctly. -/
theorem edge_normalized_neg_next_next :
    (normalize true (.next (.next (PathFormula.top : PathFormula sig)))).Holds
      edgePath.last (word edgeModel edgePath) 0 := by
  apply (normalize_holds edgeModel edgePath _ true 0 edgePath.valid_zero).mpr
  exact edge_not_next_next_top

theorem edge_normalized_next_atom :
    (normalize false (.next (.state (.atom ())))).Holds
      edgePath.last (word edgeModel edgePath) 0 := by
  apply (normalize_holds edgeModel edgePath _ false 0 edgePath.valid_zero).mpr
  exact edge_next_atom

/-- A nested state-level path quantifier remains one whole leaf. -/
theorem nested_state_syntax :
    normalize false (.state (.existsPath (.next (PathFormula.top : PathFormula sig)))) =
      Formula.pos (.existsPath (.next PathFormula.top)) := rfl

/-- The retained nested state leaf still uses genuine CTL* existential semantics. -/
theorem singleton_nested_exists_next_fails :
    ¬ (normalize false (.state (.existsPath (.next (PathFormula.top : PathFormula sig))))).Holds
      singletonPath.last (word singletonModel singletonPath) 0 := by
  unfold word
  rw [normalize_holds singletonModel singletonPath _ false 0 singletonPath.valid_zero]
  rintro ⟨path, _, hnext⟩
  exact path.edges 0 hnext.1

end Silmaril.Logic.Temporal.CTLStar.NNF.Examples
