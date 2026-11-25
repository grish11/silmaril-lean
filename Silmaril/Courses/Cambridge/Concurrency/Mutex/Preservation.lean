module

public import Silmaril.Courses.Cambridge.Concurrency.Mutex.Global
public import Silmaril.Courses.Cambridge.L1.Metatheory.Progress

/-! # Type preservation for Cambridge L1 with mutexes -/

@[expose] public section

namespace Silmaril.Courses.Cambridge.Concurrency.Mutex

theorem Step.store_domain {before after : Config} (step : Step before after) (loc : Loc) :
    loc ∈ before.shared.store ↔ loc ∈ after.shared.store := by
  induction step with
  | add | ge | deref | seqSkip | ifTrue | ifFalse | «while» | lock | unlock => rfl
  | binaryLeft _ ih => exact ih
  | binaryRight _ _ ih => exact ih
  | assignStep _ ih => exact ih
  | seqStep _ ih => exact ih
  | ifStep _ ih => exact ih
  | parallelLeft _ ih => exact ih
  | parallelRight _ ih => exact ih
  | assignValue present =>
      simp only [SharedState.write, Finmap.mem_insert]
      constructor
      · exact Or.inr
      · rintro (rfl | other)
        · exact present
        · exact other

/-- Induction on typing handles (thread) even when it is the last typing rule. -/
theorem HasType.preserve_step {Γ : TypeEnv} {e : Expr} {T : Ty} (typed : HasType Γ e T) :
    ∀ {s : SharedState} {after : Config}, Step ⟨e, s⟩ after → HasType Γ after.expr T := by
  induction typed with
  | int | bool | skip =>
      intro _ _ step
      cases step
  | add hl hr ihl ihr =>
      intro _ _ step
      cases step with
      | add => exact .int _
      | binaryLeft inner => exact .add (ihl inner) hr
      | binaryRight _ inner => exact .add hl (ihr inner)
  | ge hl hr ihl ihr =>
      intro _ _ step
      cases step with
      | ge => exact .bool _
      | binaryLeft inner => exact .ge (ihl inner) hr
      | binaryRight _ inner => exact .ge hl (ihr inner)
  | cond _ hy hn ihc _ _ =>
      intro _ _ step
      cases step with
      | ifTrue => exact hy
      | ifFalse => exact hn
      | ifStep inner => exact .cond (ihc inner) hy hn
  | assign present _ ih =>
      intro _ _ step
      cases step with
      | assignValue => exact .skip
      | assignStep inner => exact .assign present (ih inner)
  | deref =>
      intro _ _ step
      cases step
      exact .int _
  | seq _ hr ihl _ =>
      intro _ _ step
      cases step with
      | seqSkip => exact hr
      | seqStep inner => exact .seq (ihl inner) hr
  | loop ht hb _ _ =>
      intro _ _ step
      cases step
      exact .cond ht (.seq hb (.loop ht hb)) .skip
  | lock | unlock =>
      intro _ _ step
      cases step
      exact .skip
  | thread _ ih =>
      intro _ _ step
      exact .thread (ih step)
  | parallel hl hr ihl ihr =>
      intro _ _ step
      cases step with
      | parallelLeft inner => exact .parallel (ihl inner) hr
      | parallelRight inner => exact .parallel hl (ihr inner)

theorem preservation {Γ : TypeEnv} {before after : Config} {T : Ty}
    (step : Step before after) (typed : HasType Γ before.expr T)
    (covers : L1.StoreCovers Γ before.shared.store) :
    HasType Γ after.expr T ∧ L1.StoreCovers Γ after.shared.store :=
  ⟨typed.preserve_step step, fun loc present => (step.store_domain loc).mp (covers loc present)⟩

theorem preservation_steps {Γ : TypeEnv} {before after : Config} {T : Ty}
    (steps : Steps before after) (typed : HasType Γ before.expr T)
    (covers : L1.StoreCovers Γ before.shared.store) :
    HasType Γ after.expr T ∧ L1.StoreCovers Γ after.shared.store := by
  induction steps with
  | refl => exact ⟨typed, covers⟩
  | tail _ step ih => exact preservation step ih.1 ih.2

end Silmaril.Courses.Cambridge.Concurrency.Mutex
