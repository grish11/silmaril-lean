module

public import Silmaril.Logic.PDL.K.Thms
public import Silmaril.Logic.PDL.Mu.Thms

@[expose] public section
namespace Silmaril.Logic.PDL.Examples

/-- Two named steps on a three-state chain; exit deadlocks. -/
@[reducible] def chain : Model ⟨Unit, Bool⟩ where
  World := Fin 3
  step a w v := if a then w = 1 ∧ v = 2 else w = 0 ∧ v = 1
  valuation _ := {w | w = 2}
  point := 0

def sequence : Program ⟨Unit, Bool⟩ := .seq (.action false) (.action true)
def eitherStep : Program ⟨Unit, Bool⟩ := .choice (.action false) (.action true)
def reaches : Formula ⟨Unit, Bool⟩ := .diamond eitherStep.star (.atom ())

theorem sequence_reaches : Sat chain (.diamond sequence (.atom ())) :=
  ⟨2, ⟨1, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩, rfl⟩

theorem entry_not_target : ¬ Sat chain (.atom ()) := by
  change (0 : Fin 3) ≠ 2
  decide +kernel

theorem loop_reaches : Sat chain reaches := by
  refine ⟨2, ?_, rfl⟩
  exact Relation.ReflTransGen.head (Or.inl ⟨rfl, rfl⟩)
    (Relation.ReflTransGen.single (Or.inr ⟨rfl, rfl⟩))

/-- The successful loop really uses two steps, with an explicit finite length. -/
theorem loop_two_steps : Steps (eitherStep.Rel chain) 2 0 2 :=
  .tail (.tail (.zero 0) (Or.inl ⟨rfl, rfl⟩)) (Or.inr ⟨rfl, rfl⟩)

theorem sequence_test_target : Sat chain
    (.diamond (.seq sequence (.test (.atom ()))) (.atom ())) :=
  ⟨2, ⟨2, ⟨1, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩, ⟨rfl, rfl⟩⟩, rfl⟩

/-- A test never moves, so testing the exit label at entry blocks execution. -/
theorem failed_entry_test : ¬ Sat chain
    (.diamond (.seq (.test (.atom ())) sequence) (.atom ())) := by
  rintro ⟨v, ⟨u, ⟨_, hp⟩, _⟩, _⟩
  exact entry_not_target hp

theorem reversed_sequence_fails : ¬ Sat chain
    (.diamond (.seq (.action true) (.action false)) (.atom ())) := by
  rintro ⟨v, ⟨u, hu, _⟩, _⟩
  exact (by decide : (0 : Fin 3) ≠ 1) hu.1

/-- Primitive transitions fail at exit, while star still permits zero steps. -/
theorem exit_deadlock : ¬ (Formula.diamond eitherStep (.neg .bot)).Holds chain 2 := by
  rintro ⟨v, (h | h), _⟩
  · exact (by decide : (2 : Fin 3) ≠ 0) h.1
  · exact (by decide : (2 : Fin 3) ≠ 1) h.1

theorem star_at_deadlock : reaches.Holds chain 2 := ⟨2, .refl, rfl⟩

/-- A real self-loop with no labelled states: iteration cannot invent the target. -/
def unlabelledLoop : Model ⟨Unit, Unit⟩ where
  World := Unit
  step _ _ _ := True
  valuation _ := ∅
  point := ()

theorem unlabelled_loop_nonreach : ¬ Sat unlabelledLoop
    (.diamond (.star (.action ())) (.atom ())) := by
  rintro ⟨v, _, h⟩
  exact h

/-- Star translation remains correct under two nested μ binders. -/
theorem nested_loop_translation : ModalMu.Sat chain
    (Formula.diamond (.star eitherStep.star) (.atom ())).toMu := by
  apply (Formula.toMu_correct chain _ chain.point).mpr
  refine ⟨2, ?_, rfl⟩
  exact Relation.ReflTransGen.single
    ((steps_iff_closure (eitherStep.Rel chain) 0 2).mp ⟨2, loop_two_steps⟩)

theorem translated_reaches : ModalMu.Sat chain reaches.toMu :=
  (Formula.toMu_correct chain reaches chain.point).mpr loop_reaches

theorem translated_failed_test : ¬ ModalMu.Sat chain
    (Formula.diamond (.seq (.test (.atom ())) sequence) (.atom ())).toMu := by
  intro h
  exact failed_entry_test ((Formula.toMu_correct chain _ chain.point).mp h)

/-- Tests may contain modalities: this one checks reachability but stays at entry. -/
theorem modal_test_stays : Sat chain
    (.diamond (.test (.diamond sequence (.atom ()))) (.neg .bot)) :=
  ⟨0, ⟨rfl, sequence_reaches⟩, fun h => h⟩

/-- A free continuation variable survives the fresh star binder without capture. -/
def exitEnv : ModalMu.Env chain.World 1 := fun _ => {w | w = 2}

theorem free_continuation_not_captured : (0 : Fin 3) ∈
    (eitherStep.star.toMu (ModalMu.Formula.var (0 : Fin 1))).denote chain exitEnv := by
  apply (Program.toMu_correct chain eitherStep.star (.var 0) exitEnv 0).mpr
  exact ⟨2, (steps_iff_closure (eitherStep.Rel chain) 0 2).mp ⟨2, loop_two_steps⟩, rfl⟩

/-- info: 'Silmaril.Logic.ModalMu.Formula.denote_renameVars' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ModalMu.Formula.denote_renameVars
/-- info: 'Silmaril.Logic.PDL.Program.toMu_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Program.toMu_correct
/-- info: 'Silmaril.Logic.PDL.pdlToMu' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms pdlToMu
/-- info: 'Silmaril.Logic.PDL.kToPDL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms kToPDL

end Silmaril.Logic.PDL.Examples
