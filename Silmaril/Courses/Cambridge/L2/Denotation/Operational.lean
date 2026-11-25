module

public import Silmaril.Courses.Cambridge.L2.Reduction
public import Silmaril.Foundations.InfiniteTrace.Deterministic

/-! # Operational lemmas shared by the L2 denotations -/

public section

namespace Silmaril.Courses.Cambridge.L2.Denotation

theorem steps_under (plug : Expr → Expr)
    (lift : ∀ {e f : Expr} {s t : Store}, Step ⟨e, s⟩ ⟨f, t⟩ → Step ⟨plug e, s⟩ ⟨plug f, t⟩)
    {e f : Expr} {s t : Store} (run : Steps ⟨e, s⟩ ⟨f, t⟩) :
    Steps ⟨plug e, s⟩ ⟨plug f, t⟩ := by
  let wrap : Config → Config := fun c => ⟨plug c.expr, c.store⟩
  apply Relation.ReflTransGen.lift wrap ?_ _ _ run
  rintro ⟨_, _⟩ ⟨_, _⟩ step
  exact lift step

private theorem step_deterministic {before firstResult secondResult : Config}
    (first : Step before firstResult) (second : Step before secondResult) :
    firstResult = secondResult := by
  induction first generalizing secondResult with
  | add =>
      cases second with
      | add => rfl
      | binaryLeft inner => cases inner
      | binaryRight _ inner => cases inner
  | ge =>
      cases second with
      | ge => rfl
      | binaryLeft inner => cases inner
      | binaryRight _ inner => cases inner
  | binaryLeft inner ih =>
      cases second with
      | add => cases inner
      | ge => cases inner
      | binaryLeft other =>
          have equal := ih other
          cases equal
          rfl
      | binaryRight value _ => exact False.elim (value_terminal value _ inner)
  | binaryRight value inner ih =>
      cases second with
      | add => cases inner
      | ge => cases inner
      | binaryLeft other => exact False.elim (value_terminal value _ other)
      | binaryRight _ other =>
          have equal := ih other
          cases equal
          rfl
  | deref firstPresent =>
      cases second with
      | deref secondPresent =>
          have equal : _ := firstPresent.symm.trans secondPresent
          cases Option.some.inj equal
          rfl
  | assignValue =>
      cases second with
      | assignValue => rfl
      | assignStep inner => cases inner
  | assignStep inner ih =>
      cases second with
      | assignValue => cases inner
      | assignStep other =>
          have equal := ih other
          cases equal
          rfl
  | seqSkip =>
      cases second with
      | seqSkip => rfl
      | seqStep inner => cases inner
  | seqStep inner ih =>
      cases second with
      | seqSkip => cases inner
      | seqStep other =>
          have equal := ih other
          cases equal
          rfl
  | ifTrue =>
      cases second with
      | ifTrue => rfl
      | ifStep inner => cases inner
  | ifFalse =>
      cases second with
      | ifFalse => rfl
      | ifStep inner => cases inner
  | ifStep inner ih =>
      cases second with
      | ifTrue => cases inner
      | ifFalse => cases inner
      | ifStep other =>
          have equal := ih other
          cases equal
          rfl
  | «while» =>
      cases second
      rfl

  | appLeft inner ih =>
      cases second with
      | appLeft other => cases ih other; rfl
      | appRight value _ => exact False.elim (value_terminal value _ inner)
      | appFun _ => cases inner
  | appRight value inner ih =>
      cases second with
      | appLeft other => exact False.elim (value_terminal value _ other)
      | appRight _ other => cases ih other; rfl
      | appFun ready => exact False.elim (value_terminal ready _ inner)
  | appFun ready =>
      cases second with
      | appLeft inner => cases inner
      | appRight _ inner => exact False.elim (value_terminal ready _ inner)
      | appFun _ => rfl
  | letStep inner ih =>
      cases second with
      | letStep other => cases ih other; rfl
      | letValue ready => exact False.elim (value_terminal ready _ inner)
  | letValue ready =>
      cases second with
      | letStep inner => exact False.elim (value_terminal ready _ inner)
      | letValue _ => rfl
  | letRecFun =>
      cases second
      rfl

theorem stepRightUnique : Relator.RightUnique Step :=
  fun ⦃_ _ _⦄ first other => step_deterministic first other

end Silmaril.Courses.Cambridge.L2.Denotation
