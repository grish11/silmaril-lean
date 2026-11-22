module

public import Silmaril.Calculi.PERConstraints.Finite.Thms

namespace Silmaril.Calculi.PERConstraints

open Silmaril.Formats

example : choices [[false, true], [true, false]] =
    [[false, true], [false, false], [true, true], [true, false]] := rfl

example : choices ([] : List (List Bool)) = [[]] := rfl
example : choices [[true], []] = [] := rfl

example (model : PER Bool) : DISTINCTMultiset model ([false] : List Bool) ↔ model.Dom false :=
  (distinct_multiset_coe model [false]).trans (distinct_list_singleton model false)

example (model : PER Unit) :
    ¬DISTINCTMultiset model ((([false, true] : List Bool) : Multiset Bool).map fun _ => ()) := by
  change ¬DISTINCTMultiset model (([(), ()] : List Unit) : Multiset Unit)
  rw [distinct_multiset_coe, distinct_list_iff]
  simp

example : (DNF.finiteToCNF (α := Bool) [[.eq {false}], [.distinct [false, false]]]).SAT := by
  refine ⟨PER.equality Bool, (DNF.holds_finiteToCNF _ _).mpr ((DNF.holds_ofLists _ _).mpr ?_)⟩
  exact ⟨[.eq {false}], List.mem_cons_self .., by simp [AllList, All, members, Bound.Holds, EQ, PER.equality]⟩

end Silmaril.Calculi.PERConstraints
