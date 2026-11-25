module

public import Silmaril.Courses.Cambridge.L3
public import Silmaril.Courses.Cambridge.L3.Metatheory.Preservation
public import Silmaril.Foundations.InfiniteTrace

/-! # L3 contextual equivalence (chapter 8, Definition 33)

A context may bind a free name of the phrase. Plugging therefore takes place
in the named L3 syntax before scope resolution. Observations use the shared
L3 small-step relation on the resolved, closed unit programs.
-/

@[expose] public section

namespace Silmaril.Courses.Cambridge.L3

/-- The one-hole positions of the expression grammar in §5.5. -/
inductive ContextFrame where
  | binaryLeft (op : Op) (right : RawExpr)
  | binaryRight (left : RawExpr) (op : Op)
  | ifTest (yes no : RawExpr)
  | ifThen (test no : RawExpr)
  | ifElse (test yes : RawExpr)
  | assignLeft (rhs : RawExpr)
  | assignRight (lhs : RawExpr)
  | deref
  | ref
  | seqLeft (right : RawExpr)
  | seqRight (left : RawExpr)
  | whileTest (body : RawExpr)
  | whileBody (test : RawExpr)
  | lam (name : Var) (type : Ty)
  | appLeft (argument : RawExpr)
  | appRight (fn : RawExpr)
  | letValue (name : Var) (type : Ty) (body : RawExpr)
  | letBody (name : Var) (type : Ty) (value : RawExpr)
  | letRecFunction (fn parameter : Var) (domain codomain : Ty) (body : RawExpr)
  | letRecBody (fn parameter : Var) (domain codomain : Ty) (fnBody : RawExpr)
  | pairLeft (right : RawExpr)
  | pairRight (left : RawExpr)
  | fst
  | snd
  | inl (type : Ty)
  | inr (type : Ty)
  | matchScrutinee (x : Var) (A : Ty) (left : RawExpr) (y : Var) (B : Ty) (right : RawExpr)
  | matchLeft (scrutinee : RawExpr) (x : Var) (A : Ty) (y : Var) (B : Ty) (right : RawExpr)
  | matchRight (scrutinee : RawExpr) (x : Var) (A : Ty) (left : RawExpr) (y : Var) (B : Ty)
  | recordField {labels : RecordLabels} (fields : labels.Index → RawExpr) (i : labels.Index)
  | project (label : Label)

def ContextFrame.plug (context : ContextFrame) (e : RawExpr) : RawExpr :=
  match context with
  | .binaryLeft op right => .binary e op right
  | .binaryRight left op => .binary left op e
  | .ifTest yes no => .cond e yes no
  | .ifThen test no => .cond test e no
  | .ifElse test yes => .cond test yes e
  | .assignLeft rhs => .assign e rhs
  | .assignRight lhs => .assign lhs e
  | .deref => .deref e
  | .ref => .ref e
  | .seqLeft right => .seq e right
  | .seqRight left => .seq left e
  | .whileTest body => .loop e body
  | .whileBody test => .loop test e
  | .lam name type => .lam name type e
  | .appLeft argument => .app e argument
  | .appRight fn => .app fn e
  | .letValue name type body => .letE name type e body
  | .letBody name type value => .letE name type value e
  | .letRecFunction fn parameter A B body => .letRecFun fn parameter A B e body
  | .letRecBody fn parameter A B fnBody => .letRecFun fn parameter A B fnBody e
  | .pairLeft right => .pair e right
  | .pairRight left => .pair left e
  | .fst => .fst e
  | .snd => .snd e
  | .inl type => .inl e type
  | .inr type => .inr e type
  | .matchScrutinee x A left y B right => .matchSum e x A left y B right
  | .matchLeft scrutinee x A y B right => .matchSum scrutinee x A e y B right
  | .matchRight scrutinee x A left y B => .matchSum scrutinee x A left y B e
  | .recordField (labels := labels) fields i => .record labels (Function.update fields i e)
  | .project label => .project e label

/-- A general syntactic context, with the outermost frame first. -/
abbrev Context := List ContextFrame

def Context.plug (context : Context) (e : RawExpr) : RawExpr :=
  context.foldr ContextFrame.plug e

theorem Context.plug_append (outer inner : Context) (e : RawExpr) :
    Context.plug (outer ++ inner) e = Context.plug outer (Context.plug inner e) := by
  simp only [Context.plug, List.foldr_append]

def ClosedUnit (e : RawExpr) : Prop :=
  HasType ∅ .empty (e.resolve []) .unit

def UnitReturns (start : Config) : Prop :=
  ∃ finalStore, Steps start ⟨.skip, finalStore⟩

/-- Definition 33 compares convergence to unit or an actual infinite
execution. The successful evaluations may finish in different stores. -/
def UnitAgreement (left right : Expr) : Prop :=
  (InfiniteTrace Step ⟨left, ∅⟩ ∧ InfiniteTrace Step ⟨right, ∅⟩) ∨
    (UnitReturns ⟨left, ∅⟩ ∧ UnitReturns ⟨right, ∅⟩)

/-- Compare named L3 phrases by all their common closing unit contexts. -/
def ContextualEquiv (Θ : LocTypes) (Γ : VarTypes) (T : Ty) (left right : RawExpr) : Prop :=
  HasType Θ Γ (left.resolve []) T ∧ HasType Θ Γ (right.resolve []) T ∧
    ∀ context : Context, ClosedUnit (context.plug left) → ClosedUnit (context.plug right) →
      UnitAgreement ((context.plug left).resolve []) ((context.plug right).resolve [])

private theorem unit_value {Θ : LocTypes} {e : Expr}
    (typed : HasType Θ .empty e .unit) (value : IsValue e) : e = .skip := by
  cases value <;> cases typed
  rfl

theorem closedUnit_outcome {e : RawExpr} (typed : ClosedUnit e) :
    InfiniteTrace Step ⟨e.resolve [], ∅⟩ ∨ UnitReturns ⟨e.resolve [], ∅⟩ := by
  classical
  by_cases finished : UnitReturns ⟨e.resolve [], ∅⟩
  · exact Or.inr finished
  · left
    apply InfiniteTrace.coinduct (Steps ⟨e.resolve [], ∅⟩) ?_ .refl
    rintro ⟨current, store⟩ path
    obtain ⟨_, _, reachedType, reachedStore⟩ := preservation_steps path typed StoreTyped.empty
    rcases progress reachedType reachedStore with value | ⟨next, step⟩
    · have skip : current = .skip := unit_value reachedType value
      subst current
      exact (finished ⟨store, path⟩).elim
    · exact ⟨next, step, path.tail step⟩

namespace ContextualEquiv

theorem refl {Θ : LocTypes} {Γ : VarTypes} {T : Ty} {e : RawExpr}
    (typed : HasType Θ Γ (e.resolve []) T) : ContextualEquiv Θ Γ T e e := by
  refine ⟨typed, typed, fun _ closed _ => ?_⟩
  rcases closedUnit_outcome closed with divergent | returns
  · exact Or.inl ⟨divergent, divergent⟩
  · exact Or.inr ⟨returns, returns⟩

theorem symm {Θ : LocTypes} {Γ : VarTypes} {T : Ty} {left right : RawExpr}
    (equiv : ContextualEquiv Θ Γ T left right) : ContextualEquiv Θ Γ T right left := by
  refine ⟨equiv.2.1, equiv.1, fun context rightType leftType => ?_⟩
  rcases equiv.2.2 context leftType rightType with ⟨leftRun, rightRun⟩ | ⟨leftRun, rightRun⟩
  · exact Or.inl ⟨rightRun, leftRun⟩
  · exact Or.inr ⟨rightRun, leftRun⟩

/-- Preservation under plugging follows by composing syntactic contexts. -/
theorem congr {Θ Θ' : LocTypes} {Γ Γ' : VarTypes} {T U : Ty} {left right : RawExpr}
    (equiv : ContextualEquiv Θ Γ T left right) (inner : Context)
    (leftTyped : HasType Θ' Γ' ((inner.plug left).resolve []) U)
    (rightTyped : HasType Θ' Γ' ((inner.plug right).resolve []) U) :
    ContextualEquiv Θ' Γ' U (inner.plug left) (inner.plug right) := by
  refine ⟨leftTyped, rightTyped, fun outer hl hr => ?_⟩
  have compose := equiv.2.2 (outer ++ inner)
  rw [Context.plug_append, Context.plug_append] at compose
  exact compose hl hr

end ContextualEquiv

end Silmaril.Courses.Cambridge.L3
