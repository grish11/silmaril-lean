module

public import Silmaril.Courses.Cambridge.SemanticEquivalence.L1

/-! # The L1 contexts on slide 263 and the assignment case of Theorem 29 -/

@[expose] public section

namespace Silmaril.Courses.Cambridge.L1

/-- The elementary one-hole contexts listed on slide 263. -/
inductive Context where
  | binaryLeft (op : Op) (right : Expr)
  | binaryRight (left : Expr) (op : Op)
  | ifTest (yes no : Expr)
  | ifThen (test no : Expr)
  | ifElse (test yes : Expr)
  | assign (loc : Loc)
  | seqLeft (right : Expr)
  | seqRight (left : Expr)
  | whileTest (body : Expr)
  | whileBody (test : Expr)

def Context.plug (context : Context) (e : Expr) : Expr :=
  match context with
  | .binaryLeft op right => .binary e op right
  | .binaryRight left op => .binary left op e
  | .ifTest yes no => .cond e yes no
  | .ifThen test no => .cond test e no
  | .ifElse test yes => .cond test yes e
  | .assign loc => .assign loc e
  | .seqLeft right => .seq e right
  | .seqRight left => .seq left e
  | .whileTest body => .loop e body
  | .whileBody test => .loop test e

/-- The congruence obligation of Theorem 29 for one context. -/
def Context.PreservesEquiv (context : Context) : Prop :=
  ∀ {Γ : TypeEnv} {T U : Ty} {left right : Expr},
    SemanticEquiv Γ T left right →
    HasType Γ (context.plug left) U → HasType Γ (context.plug right) U →
    SemanticEquiv Γ U (context.plug left) (context.plug right)

namespace SemanticEquiv

/-- Matching RHS evaluations either both diverge under assignment or reach
the same integer and intermediate store, after which the same write fires. -/
theorem assign {Γ : TypeEnv} {left right : Expr} {loc : Loc}
    (equiv : SemanticEquiv Γ .int left right) (present : loc ∈ Γ) :
    SemanticEquiv Γ .unit (.assign loc left) (.assign loc right) := by
  obtain ⟨leftTyped, rightTyped, agree⟩ := equiv
  let wrap : Config → Config := fun state => ⟨.assign loc state.expr, state.store⟩
  have liftStep : ∀ start finish, Step start finish → Step (wrap start) (wrap finish) := by
    rintro ⟨_, _⟩ ⟨_, _⟩ step
    exact Step.assignStep step
  refine ⟨.assign present leftTyped, .assign present rightTyped, fun s covers => ?_⟩
  rcases agree s covers with ⟨leftInfinite, rightInfinite⟩ | ⟨⟨value, finalStore⟩, leftRun, rightRun⟩
  · exact Or.inl ⟨leftInfinite.map wrap liftStep, rightInfinite.map wrap liftStep⟩
  · obtain ⟨typed, finalCovers⟩ := preservation_steps leftTyped covers leftRun.1
    obtain ⟨n, rfl⟩ := typed_integer_value typed leftRun.2
    have write : Step (wrap ⟨.int n, finalStore⟩) ⟨.skip, finalStore.insert loc n⟩ :=
      .assignValue (finalCovers loc present)
    have leftPath := Relation.ReflTransGen.lift wrap liftStep _ _ leftRun.1
    have rightPath := Relation.ReflTransGen.lift wrap liftStep _ _ rightRun.1
    exact Or.inr ⟨_, ⟨leftPath.tail write, .skip⟩, ⟨rightPath.tail write, .skip⟩⟩

end SemanticEquiv

/-- The worked case of Theorem 29, with the notes' typing premises. -/
theorem Context.assign_preservesEquiv (loc : Loc) : (Context.assign loc).PreservesEquiv := by
  intro Γ T U left right equiv leftTyped _
  have assigned : HasType Γ (.assign loc left) U := leftTyped
  obtain ⟨rfl, present, rhsTyped⟩ := assigned.assign_inversion
  have sameType : T = .int := equiv.1.unique_by_rules rhsTyped
  subst T
  exact equiv.assign present

end Silmaril.Courses.Cambridge.L1
