module

public import Silmaril.Courses.Cambridge.L1.Metatheory.Safety
public import Silmaril.Courses.Cambridge.L1.OperationalInstitution
public import Silmaril.Foundations.InfiniteTrace.Deterministic

/-! # Typed L1 semantic equivalence

Sewell, *Semantics of Programming Languages* (12 February 2026), chapter 8,
slides 260–261. An initial store may allocate locations outside the typing
environment. Finite results compare the value and the entire final store.
-/

@[expose] public section

namespace Silmaril.Courses.Cambridge.L1

/-- A finite evaluation to a value in its final store. -/
def Returns (start result : Config) : Prop :=
  Steps start result ∧ IsValue result.expr

/-- The two alternatives in the notes for a fixed initial store. -/
def SameOutcome (left right : Config) : Prop :=
  (InfiniteTrace Step left ∧ InfiniteTrace Step right) ∨
    ∃ result, Returns left result ∧ Returns right result

/-- Semantic equivalence at a type and typing environment (slide 261). -/
def SemanticEquiv (Γ : TypeEnv) (T : Ty) (left right : Expr) : Prop :=
  HasType Γ left T ∧ HasType Γ right T ∧
    ∀ s, StoreCovers Γ s → SameOutcome ⟨left, s⟩ ⟨right, s⟩

theorem exists_covering_store (Γ : TypeEnv) : ∃ s, StoreCovers Γ s := by
  let entries : List (Sigma (fun _ : Loc => Int)) := Γ.keys.toList.map fun loc => ⟨loc, 0⟩
  refine ⟨entries.toFinmap, fun loc present => (Finmap.mem_list_toFinmap loc entries).mpr ?_⟩
  exact ⟨0, List.mem_map.mpr ⟨loc, Finset.mem_toList.mpr (Finmap.mem_keys.mpr present), rfl⟩⟩

private theorem stepRightUnique : Relator.RightUnique Step :=
  fun ⦃_ _ _⦄ first second => first.deterministic second

theorem Returns.result_unique {start left right : Config}
    (first : Returns start left) (second : Returns start right) : left = right := by
  cases left
  cases right
  exact RightUnique.reach_final_eq stepRightUnique first.1 second.1
    (value_terminal first.2) (value_terminal second.2)

theorem Returns.not_diverges {start result : Config} (returns : Returns start result) :
    ¬ InfiniteTrace Step start := by
  cases result
  exact RightUnique.not_infinite_of_final stepRightUnique returns.1 (value_terminal returns.2)

/-- Safety supplies a successor along every finite prefix if no value is reachable. -/
theorem diverges_or_returns {Γ : TypeEnv} {T : Ty} {e : Expr} {s : Store}
    (typed : HasType Γ e T) (covers : StoreCovers Γ s) :
    InfiniteTrace Step ⟨e, s⟩ ∨ ∃ result, Returns ⟨e, s⟩ result := by
  classical
  by_cases finished : ∃ result, Returns ⟨e, s⟩ result
  · exact Or.inr finished
  · apply Or.inl
    apply InfiniteTrace.coinduct (Steps ⟨e, s⟩) ?_ .refl
    intro state path
    rcases safety typed covers path with value | ⟨next, step⟩
    · exact (finished ⟨state, path, value⟩).elim
    · exact ⟨next, step, path.tail step⟩

/-- On typed, covered inputs, equality of finite returns captures both
alternatives. In particular, an empty return set implies actual divergence. -/
theorem sameOutcome_iff_returns {Γ : TypeEnv} {T : Ty} {left right : Expr} {s : Store}
    (leftTyped : HasType Γ left T) (rightTyped : HasType Γ right T)
    (covers : StoreCovers Γ s) :
    SameOutcome ⟨left, s⟩ ⟨right, s⟩ ↔
      ∀ result, Returns ⟨left, s⟩ result ↔ Returns ⟨right, s⟩ result := by
  constructor
  · intro same result
    rcases same with ⟨leftInfinite, rightInfinite⟩ | ⟨final, first, second⟩
    · exact iff_of_false (fun run => run.not_diverges leftInfinite)
        (fun run => run.not_diverges rightInfinite)
    · exact ⟨fun run => (first.result_unique run) ▸ second,
        fun run => (second.result_unique run) ▸ first⟩
  · intro same
    rcases diverges_or_returns leftTyped covers with leftInfinite | ⟨result, first⟩
    · rcases diverges_or_returns rightTyped covers with rightInfinite | ⟨result, second⟩
      · exact Or.inl ⟨leftInfinite, rightInfinite⟩
      · exact (((same result).mpr second).not_diverges leftInfinite).elim
    · exact Or.inr ⟨result, first, (same result).mp first⟩

theorem semanticEquiv_iff_returns {Γ : TypeEnv} {T : Ty} {left right : Expr} :
    SemanticEquiv Γ T left right ↔ HasType Γ left T ∧ HasType Γ right T ∧
      ∀ s, StoreCovers Γ s → ∀ result, Returns ⟨left, s⟩ result ↔ Returns ⟨right, s⟩ result := by
  refine ⟨fun ⟨hl, hr, same⟩ => ⟨hl, hr, fun _ covers => ?_⟩,
    fun ⟨hl, hr, same⟩ => ⟨hl, hr, fun _ covers => ?_⟩⟩
  · exact (sameOutcome_iff_returns hl hr covers).mp (same _ covers)
  · exact (sameOutcome_iff_returns hl hr covers).mpr (same _ covers)

/-- The course judgment coincides with pointwise equality of the existing
operational model's returned observations on the admitted initial stores. -/
theorem semanticEquiv_iff_may_return {Γ : TypeEnv} {T : Ty} {left right : Expr} :
    SemanticEquiv Γ T left right ↔ HasType Γ left T ∧ HasType Γ right T ∧
      ∀ s, StoreCovers Γ s → ∀ result,
        OperationalInstitution.semantics.May ⟨left, s⟩ (.returned result) ↔
        OperationalInstitution.semantics.May ⟨right, s⟩ (.returned result) := by
  simpa only [OperationalInstitution.may_return_iff, Returns] using
    (semanticEquiv_iff_returns (Γ := Γ) (T := T) (left := left) (right := right))

namespace SemanticEquiv

variable {Γ : TypeEnv} {T : Ty} {first second third : Expr}

theorem refl (typed : HasType Γ first T) : SemanticEquiv Γ T first first :=
  semanticEquiv_iff_returns.mpr ⟨typed, typed, fun _ _ _ => Iff.rfl⟩

theorem symm (same : SemanticEquiv Γ T first second) : SemanticEquiv Γ T second first := by
  obtain ⟨hl, hr, returns⟩ := semanticEquiv_iff_returns.mp same
  exact semanticEquiv_iff_returns.mpr ⟨hr, hl, fun s covers result => (returns s covers result).symm⟩

theorem trans (left : SemanticEquiv Γ T first second) (right : SemanticEquiv Γ T second third) :
    SemanticEquiv Γ T first third := by
  obtain ⟨hl, _, firstReturns⟩ := semanticEquiv_iff_returns.mp left
  obtain ⟨_, hr, secondReturns⟩ := semanticEquiv_iff_returns.mp right
  exact semanticEquiv_iff_returns.mpr ⟨hl, hr,
    fun s covers result => (firstReturns s covers result).trans (secondReturns s covers result)⟩

end SemanticEquiv

end Silmaril.Courses.Cambridge.L1
