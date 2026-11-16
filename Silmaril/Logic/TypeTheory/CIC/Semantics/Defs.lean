module

public import Silmaril.Logic.TypeTheory.CIC.Typing.Defs
public import Silmaril.Logic.TypeTheory.CIC.Semantics.ConstructorValues.Defs
public import Mathlib.SetTheory.ZFC.Basic

@[expose] public section

/-! # Concrete trace-set operations for a CIC interpretation

The value domain is Mathlib's ZFSet. Functions use Aczel-style traces rather
than ordinary graphs: applying a trace returns a set, and a function whose
values are all the empty proof value has empty trace. This is needed for
impredicative Prop. No universe-set hierarchy or full CIC interpretation is
postulated here, and no global soundness field is stored.
-/

namespace Silmaril.Logic.TypeTheory.CIC.SetSemantics

universe u

abbrev Value := ZFSet.{u}
abbrev LocalValues := List Value.{u}

/-- A function trace contains pairs `(x,y)` for every member `y` of its value at `x`. -/
noncomputable def traceLambda (A : Value.{u}) (f : A → Value.{u}) : Value.{u} :=
  ZFSet.iUnion fun x : A => ZFSet.range fun y : f x => ZFSet.pair x y

/-- Application collects the second components at an argument. It is total on raw sets. -/
def traceApply (f x : Value.{u}) : Value.{u} :=
  (ZFSet.sUnion (ZFSet.sUnion f)).sep fun y => ZFSet.pair x y ∈ f

/-- All traces whose values inhabit the corresponding dependent codomain set. -/
noncomputable def tracePi (A : Value.{u}) (B : A → Value.{u}) : Value.{u} :=
  ZFSet.range fun f : (x : A) → B x => traceLambda A (fun x => (f x : Value.{u}))

/-- A proposition is interpreted as the empty set or the singleton containing the empty proof value. -/
noncomputable def truth (P : Prop) : Value.{u} := by
  classical
  exact if P then {∅} else ∅

/-- The two truth-value sets, represented as the powerset of the singleton proof value. -/
def propositionUniverse : Value.{u} := ZFSet.powerset {∅}

/-- Semantic declarations are explicit partial assignments, with no default value for missing globals. -/
structure GlobalValues where
  constant : String → List Universe → Option Value.{u}
  inductiveType : InductiveRef → List Universe → Option Value.{u}
  constructor : InductiveRef → ℕ → List Universe → Option Value.{u}

/-- Prop and SProp use truth-value sets; Type uses the supplied universe sets.

Coinciding denotations do not add any syntactic SProp cumulativity rule.
-/
def sortValue (ρ : LevelName → ℕ) (universes : ℕ → Value.{u}) : SortExpr LevelName → Value.{u}
  | .prop | .sprop => propositionUniverse
  | .type level => universes (level.eval ρ)

/-- Explicit local closure obligations for predicative universe sets.

The trace operations and Prop closure are concrete and proved separately.
The `Semantics.Universes` layer constructs these data from finite
Grothendieck towers. The record contains no CIC typing-soundness or consistency field.
-/
structure UniverseSets (count : ℕ) where
  level : ℕ → Value.{u}
  cumulative : ∀ n m, n < count → m < count → n ≤ m → level n ⊆ level m
  successor : ∀ n, n + 1 < count → level n ∈ level (n + 1)
  proposition_sort : 1 < count → propositionUniverse ∈ level 1
  proposition_codes : ∀ n, n < count → propositionUniverse ⊆ level n
  products : ∀ (n m : ℕ) (A : Value.{u}) (B : A → Value.{u}),
    n < count → m < count → A ∈ level n → (∀ x, B x ∈ level m) → tracePi A B ∈ level (max n m)

/-- The concrete local evaluation kernel on actual CIC syntax.

Cases over tagged constructor values are interpreted when the selected
constructor context has no local definitions. Primitive projections select
fields of constructor-zero values at the actual parameter offset. Guarded
fix/cofix interpretation and constructor-local case definitions remain open.
A missing semantic declaration has no evaluation rule. No full CIC soundness
assumption or catch-all interpretation is used.
-/
inductive Evaluates (ρ : LevelName → ℕ) (universes : ℕ → Value.{u}) (globals : GlobalValues.{u}) :
    LocalValues.{u} → Expr → Value.{u} → Prop where
  | rel {values index value} : values[index]? = some value → Evaluates ρ universes globals values (.rel index) value
  | sort {values sort} : Evaluates ρ universes globals values (.sort sort) (sortValue ρ universes sort)
  | product {values na domain codomain A B} : Evaluates ρ universes globals values domain A →
      (∀ x : A, Evaluates ρ universes globals ((x : Value.{u}) :: values) codomain (B x)) →
      Evaluates ρ universes globals values (.prod na domain codomain) (tracePi A B)
  | lambda {values na domain body A f} : Evaluates ρ universes globals values domain A →
      (∀ x : A, Evaluates ρ universes globals ((x : Value.{u}) :: values) body (f x)) →
      Evaluates ρ universes globals values (.lam na domain body) (traceLambda A f)
  | application {values function argument f a} : Evaluates ρ universes globals values function f →
      Evaluates ρ universes globals values argument a →
      Evaluates ρ universes globals values (.app function argument) (traceApply f a)
  | letIn {values na value type body a b} : Evaluates ρ universes globals values value a →
      Evaluates ρ universes globals (a :: values) body b →
      Evaluates ρ universes globals values (.letIn na value type body) b
  | constant {values name ui value} : globals.constant name ui = some value →
      Evaluates ρ universes globals values (.constant name ui) value
  | inductiveType {values reference ui value} : globals.inductiveType reference ui = some value →
      Evaluates ρ universes globals values (.inductiveType reference ui) value
  | constructor {values reference index ui value} : globals.constructor reference index ui = some value →
      Evaluates ρ universes globals values (.constructor reference index ui) value
  /-- Runtime tag selection; source declaration checking separately establishes reference and field typing. -/
  | caseOf {values ci p scrutinee branches index arguments branch value} :
      Evaluates ρ universes globals values scrutinee (constructorValue index arguments) →
      branches[index]? = some branch → (∀ declaration ∈ branch.context, declaration.value = none) →
      arguments.length = ci.parameterCount + branch.context.length →
      Evaluates ρ universes globals ((arguments.drop ci.parameterCount).reverse ++ values) branch.body value →
      Evaluates ρ universes globals values (.caseOf ci p scrutinee branches) value

  /-- Field selection at the source parameter offset; checked metadata separately identifies the record. -/
  | projection {values reference scrutinee arguments value} :
      Evaluates ρ universes globals values scrutinee (constructorValue 0 arguments) →
      arguments[reference.parameterCount + reference.argument]? = some value →
      Evaluates ρ universes globals values (.projection reference scrutinee) value

/-- Local assumptions and definitions are realized by actual set values of their evaluated types. -/
inductive InterpretsLocal (ρ : LevelName → ℕ) (universes : ℕ → Value.{u}) (globals : GlobalValues.{u}) :
    Context → LocalValues.{u} → Prop where
  | nil : InterpretsLocal ρ universes globals [] []
  | assumption {Γ values na type A a} : InterpretsLocal ρ universes globals Γ values →
      Evaluates ρ universes globals values type A → a ∈ A →
      InterpretsLocal ρ universes globals ({ binder := na, type := type } :: Γ) (a :: values)
  | definition {Γ values na value type A a} : InterpretsLocal ρ universes globals Γ values →
      Evaluates ρ universes globals values type A → Evaluates ρ universes globals values value a → a ∈ A →
      InterpretsLocal ρ universes globals ({ binder := na, type := type, value := some value } :: Γ) (a :: values)

/-- A concrete denotation of the term inhabits a concrete denotation of its syntactic type. -/
def HasValueAt (ρ : LevelName → ℕ) (universes : ℕ → Value.{u}) (globals : GlobalValues.{u})
    (values : LocalValues.{u}) (term type : Expr) : Prop :=
  ∃ value A, Evaluates ρ universes globals values term value ∧
    Evaluates ρ universes globals values type A ∧ value ∈ A

/-- Each constant assignment denotes its declared type and inhabits it; declared bodies denote that same value.

This is a local declaration interpretation obligation, not a global soundness
field. Bodyless constants still require genuine inhabitants of their types.
-/
structure InterpretsConstants (ρ : LevelName → ℕ) (universes : ℕ → Value.{u})
    (globals : GlobalValues.{u}) (sig : GlobalContext) : Prop where
  declarations : ∀ name ui declaration,
    sig.environment.lookupConstant name = some declaration → sig.ValidInstance declaration.universes ui →
    ∃ A value, globals.constant name ui = some value ∧
      Evaluates ρ universes globals [] (Expr.instantiate ui declaration.type) A ∧ value ∈ A ∧
      ∀ body, declaration.body = some body → Evaluates ρ universes globals [] (Expr.instantiate ui body) value

def propositionIdentity : Expr := .lam {} (.sort .prop) (.rel 0)

def propositionIdentityType : Expr := .prod {} (.sort .prop) (.sort .prop)

end Silmaril.Logic.TypeTheory.CIC.SetSemantics
