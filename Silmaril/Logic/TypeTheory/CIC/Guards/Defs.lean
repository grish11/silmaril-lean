module

public import Silmaril.Logic.TypeTheory.CIC.Cases.Defs
public import Silmaril.Logic.TypeTheory.CIC.Positivity.Defs

@[expose] public section

/-! # Explicit structural-recursion judgments for CIC

These conservative syntactic judgments do not use MetaRocq's postulated guard
checker. They track recursive names and constructor subterms explicitly. No
completeness for Rocq's guard checker, reduction preservation, normalization or
semantic soundness is asserted by merely defining these judgments.
-/

namespace Silmaril.Logic.TypeTheory.CIC

/-- Recursive names cannot be used as values; structural bindings record remaining function arity. -/
inductive GuardBinding where
  | ordinary
  | recursive (argument : ℕ)
  | structural (arity : ℕ) (strict : Bool)
  deriving DecidableEq, Repr

def GuardBinding.AllowsVariable : GuardBinding → Prop
  | .recursive _ => False
  | _ => True

/-- A term contains no occurrence of any recursive name in the tracked context. -/
inductive RecursionFree : List GuardBinding → Expr → Prop where
  | rel {bindings index binding} : bindings[index]? = some binding →
      binding.AllowsVariable → RecursionFree bindings (.rel index)
  | sort {bindings s} : RecursionFree bindings (.sort s)
  | constant {bindings name ui} : RecursionFree bindings (.constant name ui)
  | inductiveType {bindings reference ui} : RecursionFree bindings (.inductiveType reference ui)
  | constructor {bindings reference index ui} : RecursionFree bindings (.constructor reference index ui)
  | product {bindings na A B} : RecursionFree bindings A →
      RecursionFree (.ordinary :: bindings) B → RecursionFree bindings (.prod na A B)
  | lambda {bindings na A body} : RecursionFree bindings A →
      RecursionFree (.ordinary :: bindings) body → RecursionFree bindings (.lam na A body)
  | letIn {bindings na value A body} : RecursionFree bindings value → RecursionFree bindings A →
      RecursionFree (.ordinary :: bindings) body → RecursionFree bindings (.letIn na value A body)
  | application {bindings f a} : RecursionFree bindings f → RecursionFree bindings a →
      RecursionFree bindings (.app f a)
  | caseOf {bindings ci p scrutinee branches} :
      (∀ a ∈ p.parameters, RecursionFree bindings a) →
      RecursionFree (List.replicate p.context.length .ordinary ++ bindings) p.returnType →
      RecursionFree bindings scrutinee →
      (∀ b ∈ branches, RecursionFree (List.replicate b.context.length .ordinary ++ bindings) b.body) →
      RecursionFree bindings (.caseOf ci p scrutinee branches)
  | projection {bindings reference scrutinee} : RecursionFree bindings scrutinee →
      RecursionFree bindings (.projection reference scrutinee)
  | fix {bindings definitions index} :
      (∀ d ∈ definitions, RecursionFree bindings d.type) →
      (∀ d ∈ definitions,
        RecursionFree (List.replicate definitions.length .ordinary ++ bindings) d.body) →
      RecursionFree bindings (.fix definitions index)
  | cofix {bindings definitions index} :
      (∀ d ∈ definitions, RecursionFree bindings d.type) →
      (∀ d ∈ definitions,
        RecursionFree (List.replicate definitions.length .ordinary ++ bindings) d.body) →
      RecursionFree bindings (.cofix definitions index)

/-- A positive recursive field can be a dependent function returning a mutual member. -/
inductive RecursiveField (block : MutualInductiveBody) : ℕ → ℕ → Expr → Prop where
  | conclusion {depth index body args} : block.AtIndex depth index body →
      args.length = body.type.arityArgumentCount.getD 0 →
      (∀ a ∈ args, a.isClosed depth = true) →
      RecursiveField block depth 0 (Expr.mkApps (.rel index) args)
  | product {depth arity na A B} : A.isClosed depth = true →
      RecursiveField block (depth + 1) arity B →
      RecursiveField block depth (arity + 1) (.prod na A B)
  | letIn {depth arity na value A body} : RecursiveField block depth arity (body.subst [value] 0) →
      RecursiveField block depth arity (.letIn na value A body)

/-- Ordinary fields may be ignored; only genuinely recursive positive fields become strict subterms. -/
inductive ConstructorBindings (block : MutualInductiveBody) : Context → List GuardBinding → Prop where
  | nil : ConstructorBindings block [] []
  | ordinary {decl context bindings} : ConstructorBindings block context bindings →
      ConstructorBindings block (decl :: context) (.ordinary :: bindings)
  | recursive {decl context bindings arity} : ConstructorBindings block context bindings →
      decl.value = none →
      RecursiveField block (block.parameters.length + context.length) arity decl.type →
      ConstructorBindings block (decl :: context) (.structural arity true :: bindings)

/-- Applying a positive recursive function field preserves its subterm provenance. -/
inductive StructuralSubterm (bindings : List GuardBinding) : ℕ → Bool → Expr → Prop where
  | variable {index arity strict} : bindings[index]? = some (.structural arity strict) →
      StructuralSubterm bindings arity strict (.rel index)
  | application {arity strict f a} : StructuralSubterm bindings (arity + 1) strict f →
      StructuralSubterm bindings arity strict (.app f a)

mutual

/-- Every recursive call is fully applied at its recursive argument and uses a strict subterm. -/
inductive GuardedTerm (env : GlobalEnv) (root : String) : List GuardBinding → Expr → Prop where
  | recursionFree {bindings t} : RecursionFree bindings t → GuardedTerm env root bindings t
  | call {bindings index recursiveArgument args argument} :
      bindings[index]? = some (.recursive recursiveArgument) →
      args[recursiveArgument]? = some argument →
      StructuralSubterm bindings 0 true argument →
      (∀ a ∈ args, GuardedTerm env root bindings a) →
      GuardedTerm env root bindings (Expr.mkApps (.rel index) args)
  | product {bindings na A B} : GuardedTerm env root bindings A →
      GuardedTerm env root (.ordinary :: bindings) B →
      GuardedTerm env root bindings (.prod na A B)
  | lambda {bindings na A body} : GuardedTerm env root bindings A →
      GuardedTerm env root (.ordinary :: bindings) body →
      GuardedTerm env root bindings (.lam na A body)
  | letIn {bindings na value A body} : GuardedTerm env root bindings value →
      GuardedTerm env root bindings A → GuardedTerm env root (.ordinary :: bindings) body →
      GuardedTerm env root bindings (.letIn na value A body)
  | letStructural {bindings na value A body arity strict} :
      StructuralSubterm bindings arity strict value → GuardedTerm env root bindings value →
      GuardedTerm env root bindings A →
      GuardedTerm env root (.structural arity strict :: bindings) body →
      GuardedTerm env root bindings (.letIn na value A body)
  | application {bindings f a} : GuardedTerm env root bindings f → GuardedTerm env root bindings a →
      GuardedTerm env root bindings (.app f a)
  | caseOf {bindings ci p scrutinee branches} :
      (∀ a ∈ p.parameters, GuardedTerm env root bindings a) →
      GuardedTerm env root (List.replicate p.context.length .ordinary ++ bindings) p.returnType →
      GuardedTerm env root bindings scrutinee →
      (∀ b ∈ branches,
        GuardedTerm env root (List.replicate b.context.length .ordinary ++ bindings) b.body) →
      GuardedTerm env root bindings (.caseOf ci p scrutinee branches)
  | structuralCase {bindings ci p scrutinee branches block body strict} :
      env.lookupInductive ci.inductiveRef = some (block, body) →
      ci.inductiveRef.block = root → block.recursivity = .finite →
      StructuralSubterm bindings 0 strict scrutinee →
      (∀ a ∈ p.parameters, GuardedTerm env root bindings a) →
      GuardedTerm env root (List.replicate p.context.length .ordinary ++ bindings) p.returnType →
      GuardedTerm env root bindings scrutinee → branches.length = body.constructors.length →
      (∀ (index : ℕ) (constructor : ConstructorBody) (branch : Branch Expr),
        body.constructors[index]? = some constructor → branches[index]? = some branch →
        GuardedBranch env root bindings ci.inductiveRef block p constructor branch) →
      GuardedTerm env root bindings (.caseOf ci p scrutinee branches)
  | projection {bindings reference scrutinee} : GuardedTerm env root bindings scrutinee →
      GuardedTerm env root bindings (.projection reference scrutinee)
  | fix {bindings definitions index} :
      (∀ d ∈ definitions, GuardedTerm env root bindings d.type) →
      (∀ d ∈ definitions,
        GuardedTerm env root (List.replicate definitions.length .ordinary ++ bindings) d.body) →
      GuardedTerm env root bindings (.fix definitions index)
  | cofix {bindings definitions index} :
      (∀ d ∈ definitions, GuardedTerm env root bindings d.type) →
      (∀ d ∈ definitions,
        GuardedTerm env root (List.replicate definitions.length .ordinary ++ bindings) d.body) →
      GuardedTerm env root bindings (.cofix definitions index)

/-- Branch subterm bindings come from the actual declaration, not arbitrary cached field types. -/
inductive GuardedBranch (env : GlobalEnv) (root : String) : List GuardBinding →
    InductiveRef → MutualInductiveBody → Predicate Expr LevelName → ConstructorBody → Branch Expr → Prop where
  | checked {bindings reference block p constructor branch fields} :
      Context.withoutNames branch.context = (branchDeclarationContext reference block constructor).withoutNames →
      ConstructorBindings block constructor.arguments fields →
      GuardedTerm env root (fields ++ bindings) branch.body →
      GuardedBranch env root bindings reference block p constructor branch

end

/-- The selected argument in a function signature is explicitly an inductive from the root block. -/
inductive StructuralArgument (env : GlobalEnv) (root : String) : ℕ → Expr → Prop where
  | selected {na reference ui args result block body} :
      env.lookupInductive reference = some (block, body) → reference.block = root →
      block.recursivity = .finite →
      StructuralArgument env root 0 (.prod na (Expr.mkApps (.inductiveType reference ui) args) result)
  | skip {argument na A B} : StructuralArgument env root argument B →
      StructuralArgument env root (argument + 1) (.prod na A B)
  | letIn {argument na value A body} : StructuralArgument env root argument (body.subst [value] 0) →
      StructuralArgument env root argument (.letIn na value A body)

/-- The matching function argument is the initial structural value; preceding lambdas are ordinary. -/
inductive StructuralLambda (env : GlobalEnv) (root : String) : List GuardBinding → ℕ → Expr → Prop where
  | selected {bindings na reference ui args body block indBody} :
      env.lookupInductive reference = some (block, indBody) → reference.block = root →
      block.recursivity = .finite →
      RecursionFree bindings (Expr.mkApps (.inductiveType reference ui) args) →
      GuardedTerm env root (.structural 0 false :: bindings) body →
      StructuralLambda env root bindings 0 (.lam na (Expr.mkApps (.inductiveType reference ui) args) body)
  | skip {bindings argument na A body} : RecursionFree bindings A →
      StructuralLambda env root (.ordinary :: bindings) argument body →
      StructuralLambda env root bindings (argument + 1) (.lam na A body)

/-- The mutually recursive names occupy the same reverse order as `fixContext`. -/
def recursiveBindings (Γ : Context) (definitions : List (FixDef Expr)) : List GuardBinding :=
  (definitions.map fun d => GuardBinding.recursive d.recursiveArgument).reverse ++
    List.replicate Γ.length .ordinary

/-- A concrete structural guard derivation for every member; no oracle or soundness field is stored. -/
def StructuralFix (env : GlobalEnv) (Γ : Context) (definitions : List (FixDef Expr)) : Prop :=
  definitions ≠ [] ∧ ∃ root,
    (∀ d ∈ definitions, StructuralArgument env root d.recursiveArgument d.type) ∧
    ∀ d ∈ definitions,
      StructuralLambda env root (recursiveBindings Γ definitions) d.recursiveArgument d.body

end Silmaril.Logic.TypeTheory.CIC
