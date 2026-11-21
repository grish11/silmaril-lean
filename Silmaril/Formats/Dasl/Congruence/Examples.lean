module
import Silmaril.Formats.Dasl.Congruence.Thms
import Silmaril.Formats.PER.Compatibility.Thms
import Silmaril.Formats.PER.NormalForm.Thms

namespace Silmaril.Formats.Dasl

private abbrev seed : PER Value := PER.empty Value
private abbrev onlyNull : Tree.Shape Empty Unit → Prop := (· = .leaf .null)

example : ((Tree.constructors onlyNull).generated seed).Dom .null :=
  (Tree.generated_rules seed).leaf .null rfl

example : ¬ ((Tree.constructors onlyNull).generated seed).Dom (.bool true) := by
  let justNull := (PER.equality Value).restrict (· = .null)
  have rules : Tree.Rules onlyNull justNull := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro leaf allowed
      have same := Tree.Shape.leaf.inj allowed
      cases same
      exact ⟨rfl, rfl, rfl⟩
    · intro _ _ _ impossible; cases impossible
    · intro _ _ _ impossible; cases impossible
    · intro _ _ _ impossible; cases impossible
  intro related
  have hit := (Tree.generated_le_iff (R := seed) rules).mpr (fun _ _ h => False.elim h) related
  have impossible : (Tree.bool true : Value) = .null := hit.1
  cases impossible

example (name next : String) (different : name ≠ next) :
    ¬ ((Tree.constructors (fun _ => True)).generated (PER.empty (Named String))).rel
      (.obj name .null) (.obj next .null) := by
  intro related
  have equal := Tree.generated_eq_only (R := PER.empty (Named String)) (fun _ _ h => False.elim h) related
  exact different (Tree.obj.inj equal).1

example (R : PER Value) : R.StrictlyCompatible R.singletonCompletion := PER.singletonCompletion_strict R

example (R : PER Value) : R.NormalForm (· = .null) :=
  fun _ _ hl hr _ => hl.trans hr.symm

end Silmaril.Formats.Dasl
