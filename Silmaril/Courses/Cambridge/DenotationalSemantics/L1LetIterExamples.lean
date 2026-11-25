module

import Silmaril.Courses.Cambridge.L1.LetIter.Thms

/-! Check the commuting diagram on a countdown via an independent L1
small-step derivation. Also check a missing location and an infinite loop. -/

open Silmaril (InfiniteTrace)
open Silmaril.Courses.Cambridge.L1

private def test : Expr := .binary (.deref "x") .ge (.int 1)
private def decrement : Expr := .assign "x" (.binary (.deref "x") .add (.int (-1)))
private def countdown : Expr := .loop test decrement
private def program : Expr := .seq countdown (.deref "x")

private def context : TypeEnv := (∅ : TypeEnv).insert "x" .intref
private def counter (n : Int) : Store := Store.empty.insert "x" n

private theorem locationTyped : "x" ∈ context := by simp [context]

private theorem programTyped : HasType context program .int :=
  .seq (.loop (.ge (.deref locationTyped) (.int 1))
    (.assign locationTyped (.add (.deref locationTyped) (.int (-1))))) (.deref locationTyped)

private theorem readCounter (n : Int) : Step ⟨.deref "x", counter n⟩ ⟨.int n, counter n⟩ :=
  .deref (by simp [counter])

private theorem iteration (n : Int) (positive : 1 ≤ n) :
    Steps ⟨countdown, counter n⟩ ⟨countdown, counter (n + (-1))⟩ := by
  have comparison : Step ⟨.binary (.int n) .ge (.int 1), counter n⟩ ⟨.bool true, counter n⟩ := by
    simpa [positive] using Step.ge n 1 (counter n)
  have present : "x" ∈ counter n := by simp [counter]
  have write : Step ⟨.assign "x" (.int (n + (-1))), counter n⟩
      ⟨.skip, counter (n + (-1))⟩ := by
    simpa [counter, Finmap.insert_insert] using
      Step.assignValue (loc := "x") (n := n + (-1)) present
  exact .head .while <|
    .head (.ifStep (.binaryLeft (readCounter n))) <|
    .head (.ifStep comparison) <|
    .head .ifTrue <|
    .head (.seqStep (.assignStep (.binaryLeft (readCounter n)))) <|
    .head (.seqStep (.assignStep (.add n (-1) _))) <|
    .head (.seqStep write) (.single .seqSkip)

private theorem exitLoop : Steps ⟨countdown, counter 0⟩ ⟨.skip, counter 0⟩ :=
  .head .while (.head (.ifStep (.binaryLeft (readCounter 0)))
    (.head (.ifStep (.ge 0 1 _)) (.single .ifFalse)))

private theorem programSteps : Steps ⟨program, counter 2⟩ ⟨.int 0, counter 0⟩ := by
  have loopPath : Steps ⟨countdown, counter 2⟩ ⟨.skip, counter 0⟩ :=
    (iteration 2 (by decide)).trans ((iteration 1 (by decide)).trans exitLoop)
  have framed := Relation.ReflTransGen.lift
    (fun c : Config => (⟨.seq c.expr (.deref "x"), c.store⟩ : Config))
    (fun ⟨_, _⟩ ⟨_, _⟩ step => Step.seqStep step) _ _ loopPath
  exact (framed.tail .seqSkip).tail (readCounter 0)

example : (.ok (.int 0), counter 0) ∈
    EffectfulDenotational.run (LetIter.evaluate programTyped) (counter 2) :=
  (LetIter.return_iff programTyped _ _).2 ((OperationalInstitution.may_return_iff _ _).2
    ⟨programSteps, .int 0⟩)

private theorem readTyped : HasType context (.deref "x") .int := .deref locationTyped

example : (.error (), Store.empty) ∈ EffectfulDenotational.run (LetIter.evaluate readTyped) Store.empty := by
  rw [LetIter.evaluate_agrees]
  simp [EffectfulDenotational.denote]

private def spin : Expr := .loop (.bool true) .skip

private theorem spinTyped : HasType context spin .unit := .loop (.bool true) .skip

example (s : Store) : ¬ (EffectfulDenotational.run (LetIter.evaluate spinTyped) s).Dom := by
  apply (LetIter.diverges_iff spinTyped s).2
  let unfolded := Expr.cond (.bool true) (.seq .skip spin) .skip
  apply InfiniteTrace.coinduct
    (fun c => c = ⟨spin, s⟩ ∨ c = ⟨unfolded, s⟩ ∨ c = ⟨.seq .skip spin, s⟩) ?_ (.inl rfl)
  rintro _ (rfl | rfl | rfl)
  · exact ⟨_, .while, .inr (.inl rfl)⟩
  · exact ⟨_, .ifTrue, .inr (.inr rfl)⟩
  · exact ⟨_, .seqSkip, .inl rfl⟩
