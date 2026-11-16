module

public import Silmaril.Logic.TypeTheory.CIC.Environment.Defs
public import Mathlib.Logic.Relation

@[expose] public section

/-! # CIC reduction with explicit environments and binding scopes

Adapted from MetaRocq's `PCUICReduction.v`, `PCUICCases.v` and `Environment.v`
at `c8cd46054518193103c3bb33aa6e15c7f489e72c` (MIT). These raw operational
rules do not assert that an arbitrary declaration environment is well formed.
-/

namespace Silmaril.Logic.TypeTheory.CIC

/-- Apply one term operation to the type and optional value of a local declaration. -/
def ContextDecl.mapTerms (f : Expr → Expr) (d : ContextDecl Expr) : ContextDecl Expr :=
  { d with type := f d.type, value := d.value.map f }

/-- Number of actual assumptions; local definitions consume binders but no arguments. -/
def Context.assumptionCount : Context → ℕ
  | [] => 0
  | d :: Γ => (if d.value.isNone then 1 else 0) + assumptionCount Γ

/-- Apply a context operation at each declaration's own tail scope. -/
def Context.mapAt (f : ℕ → Expr → Expr) (Γ : Context) : Context :=
  Γ.mapIdx fun i d => d.mapTerms (f (Γ.length - 1 - i))

def Context.subst (terms : List Expr) (cutoff : ℕ) (Γ : Context) : Context :=
  Γ.mapAt fun i => Term.subst terms (i + cutoff)

def Context.instantiate (universeInstance : List Universe) (Γ : Context) : Context :=
  Γ.map (ContextDecl.mapTerms (Expr.instantiate universeInstance))

/-- Replace context definitions and reindex its assumptions, as PCUIC's extended_subst. -/
def Context.extendedSubst : Context → ℕ → List Expr
  | [], _ => []
  | d :: Γ, n =>
      match d.value with
      | none => .rel n :: extendedSubst Γ (n + 1)
      | some b =>
          let s := extendedSubst Γ n
          ((b.lift (Context.assumptionCount Γ + n) s.length).subst s 0) :: s

/-- Remove local definitions from a body's context while retaining all assumptions. -/
def Context.expandLets (Γ : Context) (t : Expr) : Expr :=
  (t.lift (Context.assumptionCount Γ) Γ.length).subst (Γ.extendedSubst 0) 0

/-- Instantiate the declaration cache of a case predicate or branch. -/
def Context.instantiateCase (p : Predicate Expr LevelName) (Γ : Context) : Context :=
  Context.subst p.parameters.reverse 0 (Context.instantiate p.universeInstance Γ)

/-- Application spines are ordered from the function's first argument to its last. -/
def Expr.mkApps (t : Expr) (args : List Expr) : Expr := args.foldl .app t

def Expr.head : Expr → Expr
  | .app f _ => head f
  | t => t

/-- A constructor-headed application is the reduction trigger for structural fixpoints. -/
def Expr.IsConstructorApplication (t : Expr) : Prop :=
  match Expr.head t with
  | .constructor _ _ _ => True
  | _ => False

/-- Mutual names are substituted in reverse block order, matching de Bruijn scope. -/
def fixSubstitution (definitions : List (FixDef Expr)) : List Expr :=
  (List.range definitions.length).reverse.map (.fix definitions)

def cofixSubstitution (definitions : List (FixDef Expr)) : List Expr :=
  (List.range definitions.length).reverse.map (.cofix definitions)

def unfoldFix (definitions : List (FixDef Expr)) (index : ℕ) : Option (ℕ × Expr) := do
  let d ← definitions[index]?
  some (d.recursiveArgument, d.body.subst (fixSubstitution definitions) 0)

def unfoldCofix (definitions : List (FixDef Expr)) (index : ℕ) : Option (ℕ × Expr) := do
  let d ← definitions[index]?
  some (d.recursiveArgument, d.body.subst (cofixSubstitution definitions) 0)

/-- Each recursive name's type is lifted over the earlier declarations in its block. -/
def fixContext (definitions : List (FixDef Expr)) : Context :=
  (definitions.mapIdx fun i d =>
    { binder := d.binder, type := d.type.lift i 0 }).reverse

/-- Iota first expands local definitions, then substitutes nonparameter constructor arguments. -/
def iotaReduce (parameterCount : ℕ) (p : Predicate Expr LevelName) (args : List Expr)
    (branch : Branch Expr) : Expr :=
  (Context.expandLets (Context.instantiateCase p branch.context) branch.body).subst
    (args.drop parameterCount).reverse 0

/-- Raw one-step CIC reduction, including case/fix/cofix and reduction under binders. -/
inductive Step (env : GlobalEnv) : Context → Expr → Expr → Prop where
  | beta {Γ : Context} {na A body argument} :
      Step env Γ (.app (.lam na A body) argument) (body.subst [argument] 0)
  | zeta {Γ : Context} {na value A body} :
      Step env Γ (.letIn na value A body) (body.subst [value] 0)
  | localDelta {Γ : Context} {i decl value} :
      Γ[i]? = some decl → decl.value = some value →
      Step env Γ (.rel i) (value.lift (i + 1) 0)
  | iota {Γ : Context} {ci index ui args p branches branch} :
      branches[index]? = some branch →
      args.length = ci.parameterCount + Context.assumptionCount branch.context →
      Step env Γ (.caseOf ci p (Expr.mkApps (.constructor ci.inductiveRef index ui) args) branches)
        (iotaReduce ci.parameterCount p args branch)
  | fixUnfold {Γ : Context} {definitions index args recursiveArgument body argument} :
      unfoldFix definitions index = some (recursiveArgument, body) →
      args[recursiveArgument]? = some argument → Expr.IsConstructorApplication argument →
      Step env Γ (Expr.mkApps (.fix definitions index) args) (Expr.mkApps body args)
  | cofixCase {Γ : Context} {ci p definitions index args recursiveArgument body branches} :
      unfoldCofix definitions index = some (recursiveArgument, body) →
      Step env Γ (.caseOf ci p (Expr.mkApps (.cofix definitions index) args) branches)
        (.caseOf ci p (Expr.mkApps body args) branches)
  | cofixProjection {Γ : Context} {projection definitions index args recursiveArgument body} :
      unfoldCofix definitions index = some (recursiveArgument, body) →
      Step env Γ (.projection projection (Expr.mkApps (.cofix definitions index) args))
        (.projection projection (Expr.mkApps body args))
  | globalDelta {Γ : Context} {name decl value ui} :
      env.lookupConstant name = some decl → decl.body = some value →
      Step env Γ (.constant name ui) (Expr.instantiate ui value)
  | project {Γ : Context} {projection args ui argument} :
      args[projection.parameterCount + projection.argument]? = some argument →
      Step env Γ
        (.projection projection (Expr.mkApps (.constructor projection.inductiveRef 0 ui) args))
        argument
  | lambdaDomain {Γ : Context} {na A A' body} : Step env Γ A A' →
      Step env Γ (.lam na A body) (.lam na A' body)
  | lambdaBody {Γ : Context} {na A body body'} : Step env ({ binder := na, type := A } :: Γ) body body' →
      Step env Γ (.lam na A body) (.lam na A body')
  | letValue {Γ : Context} {na value value' A body} : Step env Γ value value' →
      Step env Γ (.letIn na value A body) (.letIn na value' A body)
  | letType {Γ : Context} {na value A A' body} : Step env Γ A A' →
      Step env Γ (.letIn na value A body) (.letIn na value A' body)
  | letBody {Γ : Context} {na value A body body'} :
      Step env ({ binder := na, type := A, value := some value } :: Γ) body body' →
      Step env Γ (.letIn na value A body) (.letIn na value A body')
  | caseParameter {Γ : Context} {ci p before after argument argument' scrutinee branches} :
      p.parameters = before ++ argument :: after → Step env Γ argument argument' →
      Step env Γ (.caseOf ci p scrutinee branches)
        (.caseOf ci { p with parameters := before ++ argument' :: after } scrutinee branches)
  | caseReturn {Γ : Context} {ci p returnType' scrutinee branches} :
      Step env (Context.instantiateCase p p.context ++ Γ) p.returnType returnType' →
      Step env Γ (.caseOf ci p scrutinee branches)
        (.caseOf ci { p with returnType := returnType' } scrutinee branches)
  | caseScrutinee {Γ : Context} {ci p scrutinee scrutinee' branches} : Step env Γ scrutinee scrutinee' →
      Step env Γ (.caseOf ci p scrutinee branches) (.caseOf ci p scrutinee' branches)
  | caseBranch {Γ : Context} {ci p scrutinee before after branch body'} :
      Step env (Context.instantiateCase p branch.context ++ Γ) branch.body body' →
      Step env Γ (.caseOf ci p scrutinee (before ++ branch :: after))
        (.caseOf ci p scrutinee (before ++ { branch with body := body' } :: after))
  | projectionBody {Γ : Context} {projection scrutinee scrutinee'} : Step env Γ scrutinee scrutinee' →
      Step env Γ (.projection projection scrutinee) (.projection projection scrutinee')
  | appFunction {Γ : Context} {f f' a} : Step env Γ f f' → Step env Γ (.app f a) (.app f' a)
  | appArgument {Γ : Context} {f a a'} : Step env Γ a a' → Step env Γ (.app f a) (.app f a')
  | productDomain {Γ : Context} {na A A' B} : Step env Γ A A' → Step env Γ (.prod na A B) (.prod na A' B)
  | productRange {Γ : Context} {na A B B'} : Step env ({ binder := na, type := A } :: Γ) B B' →
      Step env Γ (.prod na A B) (.prod na A B')
  | fixType {Γ : Context} {before after definition index type'} :
      Step env Γ definition.type type' →
      Step env Γ (.fix (before ++ definition :: after) index)
        (.fix (before ++ { definition with type := type' } :: after) index)
  | fixBody {Γ : Context} {before after definition index body'} :
      Step env (fixContext (before ++ definition :: after) ++ Γ) definition.body body' →
      Step env Γ (.fix (before ++ definition :: after) index)
        (.fix (before ++ { definition with body := body' } :: after) index)
  | cofixType {Γ : Context} {before after definition index type'} :
      Step env Γ definition.type type' →
      Step env Γ (.cofix (before ++ definition :: after) index)
        (.cofix (before ++ { definition with type := type' } :: after) index)
  | cofixBody {Γ : Context} {before after definition index body'} :
      Step env (fixContext (before ++ definition :: after) ++ Γ) definition.body body' →
      Step env Γ (.cofix (before ++ definition :: after) index)
        (.cofix (before ++ { definition with body := body' } :: after) index)

/-- Zero or more reduction steps, retaining the explicit global and local environments. -/
abbrev Steps (env : GlobalEnv) (Γ : Context) := Relation.ReflTransGen (Step env Γ)

end Silmaril.Logic.TypeTheory.CIC
