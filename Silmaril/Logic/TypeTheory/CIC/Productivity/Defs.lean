module

public import Silmaril.Logic.TypeTheory.CIC.Guards.Defs

@[expose] public section

/-! # Explicit conservative productivity of CIC corecursion

Only actual recursive constructor fields open a guarded-call position.
Arbitrary applications and observations of recursive values are excluded by
the grammar, rather than justified by an oracle. Completeness for Rocq's
checker and semantic productivity are separate theorems, not assumptions here.
-/

namespace Silmaril.Logic.TypeTheory.CIC

mutual

/-- Productive code produces a constructor before making a corecursive call observable. -/
inductive ProductiveTerm (env : GlobalEnv) (root : String) : List GuardBinding → Bool → Expr → Prop where
  | recursionFree {bindings allowed t} : RecursionFree bindings t →
      ProductiveTerm env root bindings allowed t
  | call {bindings index argument args} : bindings[index]? = some (.recursive argument) →
      (∀ a ∈ args, RecursionFree bindings a) →
      ProductiveTerm env root bindings true (Expr.mkApps (.rel index) args)
  | constructor {bindings allowed reference index ui parameters fields block body constructor} :
      env.lookupConstructor reference index = some (block, body, constructor) →
      reference.block = root → block.recursivity = .cofinite →
      parameters.length = block.parameterCount →
      (∀ a ∈ parameters, RecursionFree bindings a) →
      ProductiveArguments env root bindings block constructor.arguments fields →
      ProductiveTerm env root bindings allowed
        (Expr.mkApps (.constructor reference index ui) (parameters ++ fields))
  | lambda {bindings allowed na A body} : RecursionFree bindings A →
      ProductiveTerm env root (.ordinary :: bindings) allowed body →
      ProductiveTerm env root bindings allowed (.lam na A body)
  | letIn {bindings allowed na value A body} : RecursionFree bindings value → RecursionFree bindings A →
      ProductiveTerm env root (.ordinary :: bindings) allowed body →
      ProductiveTerm env root bindings allowed (.letIn na value A body)
  | caseOf {bindings allowed ci p scrutinee branches} :
      (∀ a ∈ p.parameters, RecursionFree bindings a) →
      RecursionFree (List.replicate p.context.length .ordinary ++ bindings) p.returnType →
      RecursionFree bindings scrutinee →
      (∀ branch ∈ branches,
        ProductiveTerm env root (List.replicate branch.context.length .ordinary ++ bindings) allowed branch.body) →
      ProductiveTerm env root bindings allowed (.caseOf ci p scrutinee branches)

/-- A positive function field is eta-expanded before entering its guarded result position. -/
inductive ProductiveField (env : GlobalEnv) (root : String) : List GuardBinding → ℕ → Expr → Prop where
  | result {bindings t} : ProductiveTerm env root bindings true t → ProductiveField env root bindings 0 t
  | lambda {bindings arity na A body} : RecursionFree bindings A →
      ProductiveField env root (.ordinary :: bindings) arity body →
      ProductiveField env root bindings (arity + 1) (.lam na A body)

/-- Constructor arguments are checked in application order; local definitions consume no arguments. -/
inductive ProductiveArguments (env : GlobalEnv) (root : String) :
    List GuardBinding → MutualInductiveBody → Context → List Expr → Prop where
  | nil {bindings block} : ProductiveArguments env root bindings block [] []
  | definition {bindings block context decl args} : decl.value.isSome = true →
      ProductiveArguments env root bindings block context args →
      ProductiveArguments env root bindings block (decl :: context) args
  | ordinary {bindings block context decl args argument} : decl.value = none →
      ProductiveArguments env root bindings block context args → RecursionFree bindings argument →
      ProductiveArguments env root bindings block (decl :: context) (args ++ [argument])
  | recursive {bindings block context decl args argument arity} : decl.value = none →
      ProductiveArguments env root bindings block context args →
      RecursiveField block (block.parameters.length + context.length) arity decl.type →
      ProductiveField env root bindings arity argument →
      ProductiveArguments env root bindings block (decl :: context) (args ++ [argument])

end

/-- Every mutual signature ultimately returns a coinductive from the same root block. -/
inductive CoinductiveResult (env : GlobalEnv) (root : String) : Expr → Prop where
  | selected {reference ui args block body} : env.lookupInductive reference = some (block, body) →
      reference.block = root → block.recursivity = .cofinite →
      CoinductiveResult env root (Expr.mkApps (.inductiveType reference ui) args)
  | product {na A B} : CoinductiveResult env root B → CoinductiveResult env root (.prod na A B)
  | letIn {na value A body} : CoinductiveResult env root (body.subst [value] 0) →
      CoinductiveResult env root (.letIn na value A body)

/-- An explicit productivity derivation for each mutual corecursive body, initially outside a constructor. -/
def ProductiveCoFix (env : GlobalEnv) (Γ : Context) (definitions : List (FixDef Expr)) : Prop :=
  definitions ≠ [] ∧ ∃ root,
    (∀ d ∈ definitions, CoinductiveResult env root d.type) ∧
    ∀ d ∈ definitions, ProductiveTerm env root (recursiveBindings Γ definitions) false d.body

end Silmaril.Logic.TypeTheory.CIC
