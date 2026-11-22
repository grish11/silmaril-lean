module

public import Silmaril.Calculi.PERConstraints.Patterns.Dasl.Examples.Defs

@[expose] public section
namespace Silmaril.Calculi.PERConstraints.Patterns.Proofs

open Silmaril.Formats Silmaril.Formats.Dasl DaslExamples

theorem selected_holds : narrowRule.Holds selectedFamily := by
  intro left right _ _ related
  have singleton : ∀ pos, left pos = Tree.null ∧ right pos = Tree.null :=
    fun pos => ⟨(related pos).1, (related pos).2.1⟩
  change (selectedFamily .output).rel (.list 2 left) (.list 2 right)
  rw [show left = allNull from funext fun pos => (singleton pos).1,
      show right = allNull from funext fun pos => (singleton pos).2]
  exact ⟨rfl, rfl, rfl⟩

private def head : Term → Term
  | .list (len + 1) children => children ⟨0, Nat.zero_lt_succ len⟩
  | _ => .null

private theorem pair_enabled (tuple : Fin 2 → Term) : pair.Enabled tuple :=
  ⟨show 0 < 2 by decide, fun _ => trivial⟩

theorem widened_fails : ¬ widenedRule.Holds selectedFamily := by
  intro holds
  have childrenRelated (pos : Fin 2) : (selectedFamily (widenedRule.holeSort pos)).Dom (mixed pos) := by
    change (selectedFamily (if pos = 0 then Index.wide else Index.narrow)).Dom (mixed pos)
    by_cases isFirst : pos = 0 <;> simp [isFirst, selectedFamily, mixed, PER.Dom, PER.restrict, PER.universal, PER.equality]
  have related := holds mixed mixed (pair_enabled mixed) (pair_enabled mixed) childrenRelated
  have same : Tree.list 2 mixed = Tree.list 2 allNull := related.1
  have impossible : (Tree.bool true : Term) = .null := congrArg head same
  cases impossible

private def listLength : Term → Nat
  | .list len _ => len
  | _ => 0

theorem selected_not_full : ¬ signature.base.constructors.Closed (selectedFamily .output) := by
  intro closed
  have related := closed (.list 1) (left := fun _ => .list 2 allNull) (right := fun _ => .list 2 allNull)
    (show 0 < 1 by decide) (show 0 < 1 by decide) (fun _ => ⟨rfl, rfl, rfl⟩)
  have same : Tree.list 1 (fun _ => .list 2 allNull) = Tree.list 2 allNull := related.1
  have impossible : 1 = 2 := congrArg listLength same
  cases impossible

theorem independentlyFull_closed (sort : Index) : signature.base.constructors.Closed (independentlyFull sort) := by
  cases sort with
  | narrow => intro shape left right enabledLeft enabledRight related; trivial
  | wide => intro shape left right enabledLeft enabledRight related; trivial
  | output =>
    intro shape left right enabledLeft enabledRight related
    cases shape with
    | list len => exact related ⟨0, enabledLeft⟩
    | _ => exact enabledLeft.elim

theorem independentlyFull_fails : ¬ narrowRule.Holds independentlyFull :=
  fun holds => holds allNull allNull (pair_enabled allNull) (pair_enabled allNull) (fun _ => trivial)

end Silmaril.Calculi.PERConstraints.Patterns.Proofs
