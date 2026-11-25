module

public import Silmaril.Courses.Cambridge.SemanticEquivalence.Congruence

/-! # Observing final-store differences (slide 262) -/

@[expose] public section

namespace Silmaril.Courses.Cambridge.L1

/-- The integer context uses a separate location to discard its argument. -/
def Context.readStore (T : Ty) (loc sink : Loc) : List Context :=
  match T with
  | .unit => [.seqLeft (.deref loc)]
  | .bool => [.ifTest (.deref loc) (.deref loc)]
  | .int => [.seqLeft (.deref loc), .assign sink]

theorem Context.readStore_typed {Γ : TypeEnv} {T : Ty} {e : Expr} {loc sink : Loc}
    (typed : HasType Γ e T) (present : loc ∈ Γ) (sinkPresent : T = .int → sink ∈ Γ) :
    HasType Γ (plugAll (readStore T loc sink) e) .int := by
  cases T
  · exact .seq (.assign (sinkPresent rfl) typed) (.deref present)
  · exact .cond typed (.deref present) (.deref present)
  · exact .seq typed (.deref present)

theorem Context.readStore_returns {Γ : TypeEnv} {T : Ty} {e : Expr} {s : Store}
    {result : Config} {loc sink : Loc} {n : Int}
    (typed : HasType Γ e T) (covers : StoreCovers Γ s) (returns : Returns ⟨e, s⟩ result)
    (lookup : Store.lookup result.store loc = some n)
    (sinkValid : T = .int → sink ∈ Γ ∧ loc ≠ sink) :
    ∃ finalStore, Returns ⟨plugAll (readStore T loc sink) e, s⟩ ⟨.int n, finalStore⟩ := by
  obtain ⟨value, finalStore⟩ := result
  obtain ⟨finalTyped, finalCovers⟩ := preservation_steps typed covers returns.1
  have evaluation := returns.evaluates
  cases T with
  | int =>
    obtain ⟨m, rfl⟩ := typed_integer_value finalTyped returns.2
    obtain ⟨present, different⟩ := sinkValid rfl
    have write := Evaluates.assign evaluation (finalCovers sink present)
    have preserved := (Store.lookup_insert_other finalStore sink loc m different).trans lookup
    exact ⟨_, (Evaluates.seq write (.deref preserved)).returns⟩
  | bool =>
    obtain ⟨b, rfl⟩ := typed_boolean_value finalTyped returns.2
    cases b
    · exact ⟨_, (Evaluates.ifFalse (yes := .deref loc) evaluation (.deref lookup)).returns⟩
    · exact ⟨_, (Evaluates.ifTrue (no := .deref loc) evaluation (.deref lookup)).returns⟩
  | unit =>
    cases typed_unit_value finalTyped returns.2
    exact ⟨_, (Evaluates.seq evaluation (.deref lookup)).returns⟩

/-- If two typed runs leave different contents at a location, plugging them
into the corresponding context makes the difference visible as an integer. -/
theorem Context.readStore_distinguishes {Γ : TypeEnv} {T : Ty} {left right : Expr} {s : Store}
    {leftResult rightResult : Config} {loc sink : Loc} {m n : Int}
    (hl : HasType Γ left T) (hr : HasType Γ right T) (covers : StoreCovers Γ s)
    (leftRun : Returns ⟨left, s⟩ leftResult) (rightRun : Returns ⟨right, s⟩ rightResult)
    (leftContents : Store.lookup leftResult.store loc = some m)
    (rightContents : Store.lookup rightResult.store loc = some n) (different : m ≠ n)
    (sinkValid : T = .int → sink ∈ Γ ∧ loc ≠ sink) :
    ¬ SemanticEquiv Γ .int (plugAll (readStore T loc sink) left) (plugAll (readStore T loc sink) right) := by
  intro equiv
  obtain ⟨leftStore, leftRun⟩ := readStore_returns hl covers leftRun leftContents sinkValid
  obtain ⟨_, rightRun⟩ := readStore_returns hr covers rightRun rightContents sinkValid
  have same := (semanticEquiv_iff_returns.mp equiv).2.2 s covers ⟨.int m, leftStore⟩
  have results := (same.mp leftRun).result_unique rightRun
  exact different (Expr.int.inj (congrArg Config.expr results))

end Silmaril.Courses.Cambridge.L1
