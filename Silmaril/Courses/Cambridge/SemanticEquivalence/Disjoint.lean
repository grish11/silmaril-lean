module

public import Silmaril.Courses.Cambridge.SemanticEquivalence.Finite

/-! # Sequencing with disjoint location environments (Exercise 42) -/

public section

namespace Silmaril.Courses.Cambridge.L1

private structure StoreFrame (Γ : TypeEnv) (s t finish matched : Store) : Prop where
  inside : ∀ loc, loc ∈ Γ → Store.lookup finish loc = Store.lookup matched loc
  left : ∀ loc, loc ∉ Γ → Store.lookup finish loc = Store.lookup s loc
  right : ∀ loc, loc ∉ Γ → Store.lookup matched loc = Store.lookup t loc

private theorem StoreFrame.unchanged {Γ : TypeEnv} {s t : Store}
    (agree : ∀ loc, loc ∈ Γ → Store.lookup s loc = Store.lookup t loc) :
    StoreFrame Γ s t s t := ⟨agree, fun _ _ => rfl, fun _ _ => rfl⟩

private theorem StoreFrame.trans {Γ : TypeEnv} {s t middle matched finish last : Store}
    (first : StoreFrame Γ s t middle matched) (second : StoreFrame Γ middle matched finish last) :
    StoreFrame Γ s t finish last :=
  ⟨second.inside, fun loc outside => (second.left loc outside).trans (first.left loc outside),
    fun loc outside => (second.right loc outside).trans (first.right loc outside)⟩

private theorem StoreFrame.write {Γ : TypeEnv} {s t finish matched : Store} {loc : Loc} {n : Int}
    (frame : StoreFrame Γ s t finish matched) (present : loc ∈ Γ) :
    StoreFrame Γ s t (finish.insert loc n) (matched.insert loc n) := by
  refine ⟨?_, ?_, ?_⟩
  · intro key member
    by_cases same : key = loc
    · subst key
      rw [Store.lookup_insert_same, Store.lookup_insert_same]
    · rw [Store.lookup_insert_other _ _ _ _ same, Store.lookup_insert_other _ _ _ _ same]
      exact frame.inside key member
  · intro key outside
    have different : key ≠ loc := fun equal => outside (equal ▸ present)
    exact (Store.lookup_insert_other _ _ _ _ different).trans (frame.left key outside)
  · intro key outside
    have different : key ≠ loc := fun equal => outside (equal ▸ present)
    exact (Store.lookup_insert_other _ _ _ _ different).trans (frame.right key outside)

private theorem Evaluates.frame {Γ : TypeEnv} {T : Ty} {e : Expr} {s t : Store} {result : Config}
    (run : Evaluates e s result) (typed : HasType Γ e T)
    (agree : ∀ loc, loc ∈ Γ → Store.lookup s loc = Store.lookup t loc) :
    ∃ matched, Evaluates e t ⟨result.expr, matched⟩ ∧ StoreFrame Γ s t result.store matched := by
  induction run generalizing t T with
  | int n _ => exact ⟨t, .int n t, .unchanged agree⟩
  | bool b _ => exact ⟨t, .bool b t, .unchanged agree⟩
  | skip => exact ⟨t, .skip t, .unchanged agree⟩
  | deref lookup =>
    cases typed with
    | deref present => exact ⟨t, .deref ((agree _ present).symm.trans lookup), .unchanged agree⟩
  | add _ _ ihl ihr =>
    cases typed with
    | add hl hr =>
      obtain ⟨_, left, first⟩ := ihl hl agree
      obtain ⟨_, right, second⟩ := ihr hr first.inside
      exact ⟨_, .add left right, first.trans second⟩
  | ge _ _ ihl ihr =>
    cases typed with
    | ge hl hr =>
      obtain ⟨_, left, first⟩ := ihl hl agree
      obtain ⟨_, right, second⟩ := ihr hr first.inside
      exact ⟨_, .ge left right, first.trans second⟩
  | assign _ allocated ih =>
    cases typed with
    | assign present rhs =>
      obtain ⟨_, rhsRun, frame⟩ := ih rhs agree
      obtain ⟨value, lookup⟩ := Finmap.mem_iff.mp allocated
      have matched := Finmap.mem_of_lookup_eq_some ((frame.inside _ present).symm.trans lookup)
      exact ⟨_, .assign rhsRun matched, frame.write present⟩
  | seq _ _ ihl ihr =>
    cases typed with
    | seq hl hr =>
      obtain ⟨_, left, first⟩ := ihl hl agree
      obtain ⟨_, right, second⟩ := ihr hr first.inside
      exact ⟨_, .seq left right, first.trans second⟩
  | ifTrue _ _ iht ihy =>
    cases typed with
    | cond ht hy _ =>
      obtain ⟨_, test, first⟩ := iht ht agree
      obtain ⟨_, yes, second⟩ := ihy hy first.inside
      exact ⟨_, .ifTrue test yes, first.trans second⟩
  | ifFalse _ _ iht ihn =>
    cases typed with
    | cond ht _ hn =>
      obtain ⟨_, test, first⟩ := iht ht agree
      obtain ⟨_, no, second⟩ := ihn hn first.inside
      exact ⟨_, .ifFalse test no, first.trans second⟩
  | whileFalse _ ih =>
    cases typed with
    | loop ht _ =>
      obtain ⟨_, test, frame⟩ := ih ht agree
      exact ⟨_, .whileFalse test, frame⟩
  | whileTrue _ _ _ iht ihb ihr =>
    cases typed with
    | loop ht hb =>
      obtain ⟨_, test, first⟩ := iht ht agree
      obtain ⟨_, body, second⟩ := ihb hb first.inside
      obtain ⟨_, rest, third⟩ := ihr (.loop ht hb) second.inside
      exact ⟨_, .whileTrue test body rest, (first.trans second).trans third⟩

private theorem HasType.weakenDomain {Γ Δ : TypeEnv} {T : Ty} {e : Expr}
    (typed : HasType Γ e T) (included : ∀ loc, loc ∈ Γ → loc ∈ Δ) : HasType Δ e T := by
  induction typed with
  | int n => exact .int n
  | bool b => exact .bool b
  | add _ _ hl hr => exact .add hl hr
  | ge _ _ hl hr => exact .ge hl hr
  | cond _ _ _ ht hy hn => exact .cond ht hy hn
  | assign present _ he => exact .assign (included _ present) he
  | deref present => exact .deref (included _ present)
  | skip => exact .skip
  | seq _ _ hl hr => exact .seq hl hr
  | loop _ _ ht hb => exact .loop ht hb

private theorem commute_eval {Γ₁ Γ₂ : TypeEnv} {e₁ e₂ : Expr} {s : Store} {result : Config}
    (h₁ : HasType Γ₁ e₁ .unit) (h₂ : HasType Γ₂ e₂ .unit)
    (disjoint : Disjoint Γ₁.keys Γ₂.keys) (covers₂ : StoreCovers Γ₂ s)
    (run : Evaluates (.seq e₁ e₂) s result) : Evaluates (.seq e₂ e₁) s result := by
  have separates : ∀ {loc : Loc}, loc ∈ Γ₁ → loc ∈ Γ₂ → False :=
    fun left right => Finset.disjoint_left.mp disjoint (Finmap.mem_keys.mpr left) (Finmap.mem_keys.mpr right)
  obtain ⟨value, finish⟩ := result
  cases run with
  | seq first second =>
    have resultType := (preservation_steps (before := ⟨e₂, _⟩) h₂ (first.coverage covers₂) second.returns.1).1
    have skip := typed_unit_value resultType second.returns.2
    cases skip
    obtain ⟨_, _, firstFrame⟩ := first.frame h₁ (t := s) (fun _ _ => rfl)
    obtain ⟨middle, right, rightFrame⟩ :=
      second.frame h₂ (t := s) (fun loc member => firstFrame.left loc (fun other => separates other member))
    obtain ⟨matched, left, leftFrame⟩ :=
      first.frame h₁ (t := middle) (fun loc member => (rightFrame.right loc (separates member)).symm)
    have same : finish = matched := by
      apply Finmap.ext_lookup
      intro loc
      by_cases inFirst : loc ∈ Γ₁
      · exact (rightFrame.left loc (separates inFirst)).trans (leftFrame.inside loc inFirst)
      · by_cases inSecond : loc ∈ Γ₂
        · exact (rightFrame.inside loc inSecond).trans (leftFrame.right loc inFirst).symm
        · exact (rightFrame.left loc inSecond).trans
            ((firstFrame.left loc inFirst).trans
              ((rightFrame.right loc inSecond).symm.trans (leftFrame.right loc inFirst).symm))
    cases same
    exact .seq right left

/-- Exercise 42. The input domain includes the union of the two environments.
The finite result comparison includes locations outside both environments. -/
theorem SemanticEquiv.seq_comm_of_disjoint {Γ₁ Γ₂ : TypeEnv} {e₁ e₂ : Expr}
    (h₁ : HasType Γ₁ e₁ .unit) (h₂ : HasType Γ₂ e₂ .unit)
    (disjoint : Disjoint Γ₁.keys Γ₂.keys) :
    SemanticEquiv (Γ₁ ∪ Γ₂) .unit (.seq e₁ e₂) (.seq e₂ e₁) := by
  have inc₁ : ∀ loc, loc ∈ Γ₁ → loc ∈ Γ₁ ∪ Γ₂ := fun _ h => Finmap.mem_union.mpr (Or.inl h)
  have inc₂ : ∀ loc, loc ∈ Γ₂ → loc ∈ Γ₁ ∪ Γ₂ := fun _ h => Finmap.mem_union.mpr (Or.inr h)
  have hl := h₁.weakenDomain inc₁
  have hr := h₂.weakenDomain inc₂
  refine semanticEquiv_iff_evaluates.mpr ⟨.seq hl hr, .seq hr hl, fun s covers result => ?_⟩
  exact ⟨commute_eval h₁ h₂ disjoint (fun loc h => covers loc (inc₂ loc h)),
    commute_eval h₂ h₁ disjoint.symm (fun loc h => covers loc (inc₁ loc h))⟩

end Silmaril.Courses.Cambridge.L1
