module

public import Silmaril.Courses.Cambridge.SemanticEquivalence.Finite

/-! # Congruence for L1 (Theorem 29 and Exercise 41)

Finite evaluations compose through each frame. For while frames, induction
on the finite evaluation derivation handles every iteration. The finite
characterization of typed equivalence also accounts for divergence.
-/

@[expose] public section

namespace Silmaril.Courses.Cambridge.L1

private theorem while_transport {Γ : TypeEnv} {test test' body body' : Expr}
    (guard : ∀ {s result}, StoreCovers Γ s → Evaluates test s result → Evaluates test' s result)
    (block : ∀ {s result}, StoreCovers Γ s → Evaluates body s result → Evaluates body' s result)
    {e : Expr} {s : Store} {result : Config} (run : Evaluates e s result) :
    e = .loop test body → StoreCovers Γ s → Evaluates (.loop test' body') s result := by
  induction run with
  | whileFalse testRun _ =>
    intro shape covers
    cases shape
    exact .whileFalse (guard covers testRun)
  | whileTrue testRun bodyRun _ _ _ ih =>
    intro shape covers
    cases shape
    have afterTest := testRun.coverage covers
    exact .whileTrue (guard covers testRun) (block afterTest bodyRun) (ih rfl (bodyRun.coverage afterTest))
  | _ =>
    intro shape
    cases shape

private theorem Context.transport {Γ : TypeEnv} {left right : Expr} (context : Context)
    (replace : ∀ {s result}, StoreCovers Γ s → Evaluates left s result → Evaluates right s result)
    {s : Store} {result : Config} (covers : StoreCovers Γ s)
    (run : Evaluates (context.plug left) s result) :
    Evaluates (context.plug right) s result := by
  cases context
  case binaryLeft op other =>
    cases run with
    | add hl hr => exact .add (replace covers hl) hr
    | ge hl hr => exact .ge (replace covers hl) hr
  case binaryRight other op =>
    cases run with
    | add hl hr => exact .add hl (replace (hl.coverage covers) hr)
    | ge hl hr => exact .ge hl (replace (hl.coverage covers) hr)
  case ifTest yes no =>
    cases run with
    | ifTrue ht hy => exact .ifTrue (replace covers ht) hy
    | ifFalse ht hn => exact .ifFalse (replace covers ht) hn
  case ifThen test no =>
    cases run with
    | ifTrue ht hy => exact .ifTrue ht (replace (ht.coverage covers) hy)
    | ifFalse ht hn => exact .ifFalse ht hn
  case ifElse test yes =>
    cases run with
    | ifTrue ht hy => exact .ifTrue ht hy
    | ifFalse ht hn => exact .ifFalse ht (replace (ht.coverage covers) hn)
  case assign loc =>
    cases run with
    | assign rhs present => exact .assign (replace covers rhs) present
  case seqLeft other =>
    cases run with
    | seq hl hr => exact .seq (replace covers hl) hr
  case seqRight other =>
    cases run with
    | seq hl hr => exact .seq hl (replace (hl.coverage covers) hr)
  case whileTest body =>
    exact while_transport (fun h hr => replace h hr) (fun _ hr => hr) run rfl covers
  case whileBody test =>
    exact while_transport (fun _ hr => hr) (fun h hr => replace h hr) run rfl covers

/-- Theorem 29 for every elementary context on slide 263. -/
theorem Context.preservesEquiv (context : Context) : context.PreservesEquiv := by
  intro Γ T U left right equiv leftTyped rightTyped
  obtain ⟨_, _, same⟩ := semanticEquiv_iff_evaluates.mp equiv
  exact semanticEquiv_iff_evaluates.mpr ⟨leftTyped, rightTyped, fun s covers result =>
    ⟨context.transport (fun h run => (same _ h _).mp run) covers,
      context.transport (fun h run => (same _ h _).mpr run) covers⟩⟩

/-- The outermost context comes first. -/
def Context.plugAll (contexts : List Context) (e : Expr) : Expr :=
  contexts.foldr Context.plug e

private theorem Context.transportAll {Γ : TypeEnv} {left right : Expr} (contexts : List Context)
    (replace : ∀ {s result}, StoreCovers Γ s → Evaluates left s result → Evaluates right s result)
    {s : Store} {result : Config} (covers : StoreCovers Γ s)
    (run : Evaluates (Context.plugAll contexts left) s result) :
    Evaluates (Context.plugAll contexts right) s result := by
  induction contexts generalizing s result with
  | nil => exact replace covers run
  | cons frame frames ih =>
    exact frame.transport (fun covered inner => ih covered inner) covers run

theorem Context.plugAll_preservesEquiv {Γ : TypeEnv} {T U : Ty} {left right : Expr}
    (contexts : List Context) (equiv : SemanticEquiv Γ T left right)
    (leftTyped : HasType Γ (plugAll contexts left) U) (rightTyped : HasType Γ (plugAll contexts right) U) :
    SemanticEquiv Γ U (plugAll contexts left) (plugAll contexts right) := by
  obtain ⟨_, _, same⟩ := semanticEquiv_iff_evaluates.mp equiv
  exact semanticEquiv_iff_evaluates.mpr ⟨leftTyped, rightTyped, fun s covers result =>
    ⟨transportAll contexts (fun h run => (same _ h _).mp run) covers,
      transportAll contexts (fun h run => (same _ h _).mpr run) covers⟩⟩

end Silmaril.Courses.Cambridge.L1
