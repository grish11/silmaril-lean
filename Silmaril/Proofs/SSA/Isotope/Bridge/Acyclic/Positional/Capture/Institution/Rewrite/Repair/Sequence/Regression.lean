module

import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Sequence.Model.Thms

namespace Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Sequence

private abbrev exits : List Sorts := [.unit]

example : Repaired false (EmptySequencing.equation exits) ∧
    ¬ Derivable false (EmptySequencing.equation exits) :=
  ⟨EmptySequencing.repaired exits, EmptySequencing.unprovable exits⟩

example : Repaired false (equation exits
    (.emit false (.emit true (.stop false true)))
    (.emit false (.emit true (.stop false false)))) :=
  (repaired_iff_normal _ _ _).mpr rfl

example : ¬ Repaired false (equation exits
    (.emit false (.emit true (.stop false true)))
    (.emit true (.emit false (.stop false false)))) := by
  intro h
  have order := (repaired_iff_normal _ _ _).mp h
  cases order

example : ¬ Repaired false (equation exits
    (.emit true (.stop false true))
    (.emit true (.stop true false))) := by
  intro h
  have terminal := (repaired_iff_normal _ _ _).mp h
  cases terminal

end Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Sequence
