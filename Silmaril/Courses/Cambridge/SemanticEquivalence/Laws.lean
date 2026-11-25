module

public import Silmaril.Courses.Cambridge.SemanticEquivalence.Finite

/-! # Sequencing and conditional laws (slides 255 and 266) -/

public section

namespace Silmaril.Courses.Cambridge.L1

namespace SemanticEquiv

/-- Conjecture 30. Both groupings visit the same intermediate stores in order. -/
theorem seq_assoc {Γ : TypeEnv} {T : Ty} {e₁ e₂ e₃ : Expr}
    (h₁ : HasType Γ e₁ .unit) (h₂ : HasType Γ e₂ .unit) (h₃ : HasType Γ e₃ T) :
    SemanticEquiv Γ T (.seq e₁ (.seq e₂ e₃)) (.seq (.seq e₁ e₂) e₃) := by
  refine semanticEquiv_iff_evaluates.mpr ⟨.seq h₁ (.seq h₂ h₃), .seq (.seq h₁ h₂) h₃, ?_⟩
  intro s _ result
  constructor <;> intro run
  · cases run with
    | seq first rest =>
      cases rest with
      | seq second third => exact .seq (.seq first second) third
  · cases run with
    | seq initial third =>
      cases initial with
      | seq first second => exact .seq first (.seq second third)

/-- Conjecture 31. Move the continuation into the selected branch. -/
theorem cond_seq {Γ : TypeEnv} {T : Ty} {test yes no next : Expr}
    (ht : HasType Γ test .bool) (hy : HasType Γ yes .unit) (hn : HasType Γ no .unit)
    (he : HasType Γ next T) :
    SemanticEquiv Γ T (.seq (.cond test yes no) next)
      (.cond test (.seq yes next) (.seq no next)) := by
  refine semanticEquiv_iff_evaluates.mpr ⟨.seq (.cond ht hy hn) he,
    .cond ht (.seq hy he) (.seq hn he), ?_⟩
  intro s _ result
  constructor <;> intro run
  · cases run with
    | seq branch continuation =>
      cases branch with
      | ifTrue ht hy => exact .ifTrue ht (.seq hy continuation)
      | ifFalse ht hn => exact .ifFalse ht (.seq hn continuation)
  · cases run with
    | ifTrue ht branch =>
      cases branch with
      | seq hy continuation => exact .seq (.ifTrue ht hy) continuation
    | ifFalse ht branch =>
      cases branch with
      | seq hn continuation => exact .seq (.ifFalse ht hn) continuation

/-- Slide 255's fourth candidate keeps the initial phrase before the guard. -/
theorem seq_cond_guard {Γ : TypeEnv} {T : Ty} {first test yes no : Expr}
    (hf : HasType Γ first .unit) (ht : HasType Γ test .bool)
    (hy : HasType Γ yes T) (hn : HasType Γ no T) :
    SemanticEquiv Γ T (.seq first (.cond test yes no)) (.cond (.seq first test) yes no) := by
  refine semanticEquiv_iff_evaluates.mpr ⟨.seq hf (.cond ht hy hn), .cond (.seq hf ht) hy hn, ?_⟩
  intro s _ result
  constructor <;> intro run
  · cases run with
    | seq first branch =>
      cases branch with
      | ifTrue ht hy => exact .ifTrue (.seq first ht) hy
      | ifFalse ht hn => exact .ifFalse (.seq first ht) hn
  · cases run with
    | ifTrue before hy =>
      cases before with
      | seq first ht => exact .seq first (.ifTrue ht hy)
    | ifFalse before hn =>
      cases before with
      | seq first ht => exact .seq first (.ifFalse ht hn)

end SemanticEquiv

/-- Conjecture 32 fails when the prefix writes the location read by the guard.
Both expressions finish with the same store, but the guard sees different values. -/
theorem conjecture32_counterexample :
    ∃ (Γ : TypeEnv) (first test yes no : Expr),
      HasType Γ first .unit ∧ HasType Γ test .bool ∧ HasType Γ yes .int ∧ HasType Γ no .int ∧
      ¬ SemanticEquiv Γ .int (.seq first (.cond test yes no))
        (.cond test (.seq first yes) (.seq first no)) := by
  let loc : Loc := "l"
  let Γ : TypeEnv := (∅ : TypeEnv).insert loc .intref
  let store : Store := (∅ : Store).insert loc 0
  let first := Expr.assign loc (.int 1)
  let test := Expr.binary (.deref loc) .ge (.int 1)
  have present : loc ∈ Γ := Finmap.mem_insert.mpr (Or.inl rfl)
  refine ⟨Γ, first, test, .int 1, .int 0, .assign present (.int 1),
    .ge (.deref present) (.int 1), .int 1, .int 0, ?_⟩
  intro equiv
  have allocated : loc ∈ store := Finmap.mem_insert.mpr (Or.inl rfl)
  have covers : StoreCovers Γ store := by
    intro key member
    rcases Finmap.mem_insert.mp member with rfl | inEmpty
    · exact allocated
    · exact (Finmap.notMem_empty inEmpty).elim
  have setOne : Evaluates first store ⟨.skip, store.insert loc 1⟩ :=
    .assign (.int 1 store) allocated
  have left : Evaluates (.seq first (.cond test (.int 1) (.int 0))) store
      ⟨.int 1, store.insert loc 1⟩ :=
    .seq setOne (.ifTrue (.ge (.deref (Store.lookup_insert_same store loc 1)) (.int 1 _)) (.int 1 _))
  have right : Evaluates (.cond test (.seq first (.int 1)) (.seq first (.int 0))) store
      ⟨.int 0, store.insert loc 1⟩ :=
    .ifFalse (.ge (.deref (Store.lookup_insert_same (∅ : Store) loc 0)) (.int 1 _)) (.seq setOne (.int 0 _))
  have agree := (semanticEquiv_iff_evaluates.mp equiv).2.2 store covers ⟨.int 1, store.insert loc 1⟩
  have equal := (agree.mp left).returns.result_unique right.returns
  exact Int.one_ne_zero (Expr.int.inj (congrArg Config.expr equal))

end Silmaril.Courses.Cambridge.L1
