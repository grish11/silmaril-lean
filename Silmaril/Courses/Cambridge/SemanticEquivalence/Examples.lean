module

public import Silmaril.Courses.Cambridge.SemanticEquivalence.Contexts

/-! # L1 examples from slides 253–255 and 265 -/

@[expose] public section

namespace Silmaril.Courses.Cambridge.L1.EquivalenceExamples

theorem two_plus_two (Γ : TypeEnv) :
    SemanticEquiv Γ .int (.binary (.int 2) .add (.int 2)) (.int 4) := by
  refine ⟨.add (.int 2) (.int 2), .int 4, fun s _ => Or.inr ?_⟩
  exact ⟨⟨.int 4, s⟩, ⟨.single (.add 2 2 s), .int 4⟩, ⟨.refl, .int 4⟩⟩

def writeZero (loc : Loc) : Expr :=
  .seq (.assign loc (.int 0)) (.int 4)

def writeOne (loc : Loc) : Expr :=
  .seq (.assign loc (.int 1)) (.binary (.int 3) .add (.deref loc))

theorem writeZero_returns {loc : Loc} {s : Store} (allocated : loc ∈ s) :
    Returns ⟨writeZero loc, s⟩ ⟨.int 4, s.insert loc 0⟩ :=
  ⟨.head (.seqStep (.assignValue allocated)) (.single .seqSkip), .int 4⟩

theorem writeOne_returns {loc : Loc} {s : Store} (allocated : loc ∈ s) :
    Returns ⟨writeOne loc, s⟩ ⟨.int 4, s.insert loc 1⟩ :=
  ⟨.head (.seqStep (.assignValue allocated)) (.head .seqSkip
    (.head (.binaryRight (.int 3) (.deref (Store.lookup_insert_same s loc 1)))
      (.single (.add 3 1 _)))), .int 4⟩

/-- The same result expression `4` leaves different contents at `loc`. -/
theorem writeZero_not_equiv_writeOne (Γ : TypeEnv) (loc : Loc) :
    ¬ SemanticEquiv Γ .int (writeZero loc) (writeOne loc) := by
  intro equiv
  have present : loc ∈ Γ := equiv.1.seq_inversion.1.assign_inversion.2.1
  obtain ⟨s, covers⟩ := exists_covering_store Γ
  have allocated := covers loc present
  have same := (semanticEquiv_iff_returns.mp equiv).2.2 s covers ⟨.int 4, s.insert loc 0⟩
  have sameResult := (same.mp (writeZero_returns allocated)).result_unique (writeOne_returns allocated)
  have stored := congrArg (fun result : Config => Store.lookup result.store loc) sameResult
  simp only [Store.lookup_insert_same] at stored
  exact (by decide : (0 : Int) ≠ 1) (Option.some.inj stored)

private theorem addRead_returns {e : Expr} {s finalStore : Store} {loc : Loc} {n : Int}
    (prefixRun : Returns ⟨e, s⟩ ⟨.int 4, finalStore⟩)
    (lookup : Store.lookup finalStore loc = some n) :
    Returns ⟨(Context.binaryLeft .add (.deref loc)).plug e, s⟩ ⟨.int (4 + n), finalStore⟩ := by
  let wrap : Config → Config := fun c => ⟨.binary c.expr .add (.deref loc), c.store⟩
  have liftStep : ∀ start finish, Step start finish → Step (wrap start) (wrap finish) := by
    rintro ⟨_, _⟩ ⟨_, _⟩ step
    exact .binaryLeft step
  have path := Relation.ReflTransGen.lift wrap liftStep _ _ prefixRun.1
  exact ⟨(path.tail (.binaryRight (.int 4) (.deref lookup))).tail (.add 4 n _), .int _⟩

/-- Slide 254's context observes the otherwise hidden difference. -/
theorem read_context_distinguishes {loc : Loc} {s : Store} (allocated : loc ∈ s) :
    let context := Context.binaryLeft .add (.deref loc)
    Returns ⟨context.plug (writeZero loc), s⟩ ⟨.int 4, s.insert loc 0⟩ ∧
    Returns ⟨context.plug (writeOne loc), s⟩ ⟨.int 5, s.insert loc 1⟩ :=
  ⟨addRead_returns (writeZero_returns allocated) (Store.lookup_insert_same s loc 0),
    addRead_returns (writeOne_returns allocated) (Store.lookup_insert_same s loc 1)⟩

/-- The chapter 2 grammar expresses subtraction of one as addition of `-1`. -/
def addTo (loc : Loc) (delta : Int) : Expr :=
  .assign loc (.binary (.deref loc) .add (.int delta))

private theorem addTo_returns {loc : Loc} {s : Store} {n : Int}
    (delta : Int) (lookup : Store.lookup s loc = some n) :
    Returns ⟨addTo loc delta, s⟩ ⟨.skip, s.insert loc (n + delta)⟩ :=
  ⟨.head (.assignStep (.binaryLeft (.deref lookup))) (.head (.assignStep (.add n delta s))
    (.single (.assignValue (Finmap.mem_of_lookup_eq_some lookup)))), .skip⟩

private theorem insert_current {loc : Loc} {s : Store} {n : Int}
    (lookup : Store.lookup s loc = some n) : s.insert loc n = s := by
  apply Finmap.ext_lookup
  intro key
  change Store.lookup (s.insert loc n) key = Store.lookup s key
  by_cases same : key = loc
  · subst key
    rw [Store.lookup_insert_same, lookup]
  · exact Store.lookup_insert_other s loc key n same

theorem increment_then_decrement {Γ : TypeEnv} {loc : Loc} (present : loc ∈ Γ) :
    SemanticEquiv Γ .unit (.seq (addTo loc 1) (addTo loc (-1))) (.assign loc (.deref loc)) := by
  have typedAdd (delta : Int) : HasType Γ (addTo loc delta) .unit :=
    .assign present (.add (.deref present) (.int delta))
  refine ⟨.seq (typedAdd 1) (typedAdd (-1)), .assign present (.deref present), fun s covers => ?_⟩
  have allocated := covers loc present
  obtain ⟨n, lookup⟩ := Finmap.mem_iff.mp allocated
  have first := addTo_returns 1 lookup
  have second := addTo_returns (-1) (Store.lookup_insert_same s loc (n + 1))
  let wrap : Config → Config := fun c => ⟨.seq c.expr (addTo loc (-1)), c.store⟩
  have liftStep : ∀ start finish, Step start finish → Step (wrap start) (wrap finish) := by
    rintro ⟨_, _⟩ ⟨_, _⟩ step
    exact .seqStep step
  have firstPath := Relation.ReflTransGen.lift wrap liftStep _ _ first.1
  have restored : (s.insert loc (n + 1)).insert loc (n + 1 + (-1)) = s := by
    rw [Finmap.insert_insert, show n + 1 + (-1) = n by omega, insert_current lookup]
  have left : Returns ⟨.seq (addTo loc 1) (addTo loc (-1)), s⟩ ⟨.skip, s⟩ := by
    refine ⟨?_, .skip⟩
    have path := (firstPath.tail .seqSkip).trans second.1
    rwa [restored] at path
  have right : Returns ⟨.assign loc (.deref loc), s⟩ ⟨.skip, s⟩ := by
    refine ⟨?_, .skip⟩
    have path : Steps ⟨.assign loc (.deref loc), s⟩ ⟨.skip, s.insert loc n⟩ :=
      .head (.assignStep (.deref lookup)) (.single (.assignValue allocated))
    rwa [insert_current lookup] at path
  exact Or.inr ⟨⟨.skip, s⟩, left, right⟩

def endless : Expr := .loop (.bool true) .skip

theorem endless_diverges (s : Store) : InfiniteTrace Step ⟨endless, s⟩ := by
  let guard : Expr := .cond (.bool true) (.seq .skip endless) .skip
  apply InfiniteTrace.coinduct
    (fun c => c = ⟨endless, s⟩ ∨ c = ⟨guard, s⟩ ∨ c = ⟨.seq .skip endless, s⟩) ?_ (Or.inl rfl)
  rintro _ (rfl | rfl | rfl)
  · exact ⟨⟨guard, s⟩, .while, Or.inr (Or.inl rfl)⟩
  · exact ⟨⟨.seq .skip endless, s⟩, .ifTrue, Or.inr (Or.inr rfl)⟩
  · exact ⟨⟨endless, s⟩, .seqSkip, Or.inl rfl⟩

theorem endless_equiv_seq (Γ : TypeEnv) : SemanticEquiv Γ .unit endless (.seq .skip endless) :=
  ⟨.loop (.bool true) .skip, .seq .skip (.loop (.bool true) .skip), fun s _ =>
    Or.inl ⟨endless_diverges s, InfiniteTrace.fold .seqSkip (endless_diverges s)⟩⟩

theorem endless_not_equiv_skip (Γ : TypeEnv) : ¬ SemanticEquiv Γ .unit endless .skip := by
  intro equiv
  obtain ⟨s, covers⟩ := exists_covering_store Γ
  have skipReturns : Returns ⟨.skip, s⟩ ⟨.skip, s⟩ := ⟨.refl, .skip⟩
  have same := (semanticEquiv_iff_returns.mp equiv).2.2 s covers ⟨.skip, s⟩
  exact ((same.mpr skipReturns).not_diverges) (endless_diverges s)

end Silmaril.Courses.Cambridge.L1.EquivalenceExamples
