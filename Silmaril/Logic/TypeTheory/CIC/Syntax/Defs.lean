module

public import Silmaril.Logic.TypeTheory.CIC.Universes.Defs

@[expose] public section

/-! # Raw CIC syntax with PCUIC binding conventions

Adapted from `PCUICAst.v` and `BasicAst.v` in MetaRocq at
`c8cd46054518193103c3bb33aa6e15c7f489e72c` (MIT; see
`licenses/MetaRocq-MIT.txt`). This layer covers the CIC constructors, including
indexed-inductive references, dependent cases and mutual fix/cofix bodies.
Machine primitives and elaborator evars are outside this syntax profile.
Raw syntax alone certifies neither positivity, guardedness nor typing.
-/

namespace Silmaril.Logic.TypeTheory.CIC

universe u v

/-- Binder relevance is separate from the binder's optional printable name. -/
inductive Relevance where
  | relevant
  | irrelevant
  deriving DecidableEq, Repr

/-- A binder annotation; anonymous binders carry no name. -/
structure Binder where
  name : Option String := none
  relevance : Relevance := .relevant
  deriving DecidableEq, Repr

/-- A global reference into a mutual inductive block. -/
structure InductiveRef where
  block : String
  index : ℕ
  deriving DecidableEq, Repr

/-- Information attached to a dependent case. -/
structure CaseInfo where
  inductiveRef : InductiveRef
  parameterCount : ℕ
  relevance : Relevance
  deriving DecidableEq, Repr

/-- A primitive-record projection reference. -/
structure ProjectionRef where
  inductiveRef : InductiveRef
  parameterCount : ℕ
  argument : ℕ
  deriving DecidableEq, Repr

/-- A local assumption or definition. Context lists put the newest entry first. -/
structure ContextDecl (Term : Type u) where
  binder : Binder
  type : Term
  value : Option Term := none
  deriving DecidableEq, Repr

/-- The dependent motive of a case, including its declaration-context metadata. -/
structure Predicate (Term : Type u) (Level : Type v) where
  parameters : List Term
  universeInstance : List (UniverseExpr Level)
  context : List (ContextDecl Term)
  returnType : Term
  deriving DecidableEq, Repr

/-- One branch, whose body binds every declaration in its branch context. -/
structure Branch (Term : Type u) where
  context : List (ContextDecl Term)
  body : Term
  deriving DecidableEq, Repr

/-- A member of a mutual recursive block; body scope includes all block names. -/
structure FixDef (Term : Type u) where
  binder : Binder
  type : Term
  body : Term
  recursiveArgument : ℕ
  deriving DecidableEq, Repr

/-- PCUIC-shaped raw CIC syntax, parameterized by universe-level names.

Global names are abstract strings. Term variables are de Bruijn indices, with
zero the nearest binder. Case predicate/branch contexts are metadata expressed
in their declaration-parameter context, not in the current term context.
-/
inductive Term (Level : Type u) where
  | rel (index : ℕ)
  | free (name : String)
  | sort (sort : SortExpr Level)
  | prod (binder : Binder) (domain range : Term Level)
  | lam (binder : Binder) (domain body : Term Level)
  | letIn (binder : Binder) (value type body : Term Level)
  | app (function argument : Term Level)
  | constant (name : String) (universeInstance : List (UniverseExpr Level))
  | inductiveType (reference : InductiveRef) (universeInstance : List (UniverseExpr Level))
  | constructor (reference : InductiveRef) (index : ℕ) (universeInstance : List (UniverseExpr Level))
  | caseOf (info : CaseInfo) (predicate : Predicate (Term Level) Level)
      (scrutinee : Term Level) (branches : List (Branch (Term Level)))
  | projection (reference : ProjectionRef) (scrutinee : Term Level)
  | fix (definitions : List (FixDef (Term Level))) (index : ℕ)
  | cofix (definitions : List (FixDef (Term Level))) (index : ℕ)
  deriving Repr

namespace Term

/-- Lift free de Bruijn indices at or above `cutoff` by `amount`.

As in PCUIC, case context metadata is unchanged. The motive return binds its
predicate context; branch bodies bind their branch contexts. Mutual recursive
bodies bind the entire mutual block, while their declared types do not.
-/
def lift {Level : Type u} (amount cutoff : ℕ) : Term Level → Term Level
  | .rel i => .rel (if cutoff ≤ i then i + amount else i)
  | .free x => .free x
  | .sort s => .sort s
  | .prod na A B => .prod na (lift amount cutoff A) (lift amount (cutoff + 1) B)
  | .lam na A b => .lam na (lift amount cutoff A) (lift amount (cutoff + 1) b)
  | .letIn na a A b =>
      .letIn na (lift amount cutoff a) (lift amount cutoff A) (lift amount (cutoff + 1) b)
  | .app f a => .app (lift amount cutoff f) (lift amount cutoff a)
  | .constant c ui => .constant c ui
  | .inductiveType i ui => .inductiveType i ui
  | .constructor i c ui => .constructor i c ui
  | .caseOf ci p c brs =>
      .caseOf ci
        { p with parameters := p.parameters.map (fun a => lift amount cutoff a),
                 returnType := lift amount (p.context.length + cutoff) p.returnType }
        (lift amount cutoff c)
        (brs.map fun b => { b with body := lift amount (b.context.length + cutoff) b.body })
  | .projection p c => .projection p (lift amount cutoff c)
  | .fix ds i =>
      .fix (ds.map fun d => { d with
        type := lift amount cutoff d.type
        body := lift amount (ds.length + cutoff) d.body }) i
  | .cofix ds i =>
      .cofix (ds.map fun d => { d with
        type := lift amount cutoff d.type
        body := lift amount (ds.length + cutoff) d.body }) i

termination_by t => sizeOf t
decreasing_by
  all_goals simp_wf
  all_goals try omega
  all_goals
    first
    | have h := List.sizeOf_lt_of_mem (by assumption)
      try cases p
      try cases b
      try cases d
      simp_all only [Predicate.mk.sizeOf_spec, Branch.mk.sizeOf_spec, FixDef.mk.sizeOf_spec]
      omega
    | cases p
      simp only [Predicate.mk.sizeOf_spec]
      omega

/-- PCUIC parallel substitution at a cutoff; inserted terms are lifted under binders. -/
def subst {Level : Type u} (replacements : List (Term Level)) (cutoff : ℕ) :
    Term Level → Term Level
  | .rel i =>
      if i < cutoff then .rel i
      else match replacements[i - cutoff]? with
        | some t => t.lift cutoff 0
        | none => .rel (i - replacements.length)
  | .free x => .free x
  | .sort s => .sort s
  | .prod na A B => .prod na (subst replacements cutoff A) (subst replacements (cutoff + 1) B)
  | .lam na A b => .lam na (subst replacements cutoff A) (subst replacements (cutoff + 1) b)
  | .letIn na a A b => .letIn na (subst replacements cutoff a) (subst replacements cutoff A)
      (subst replacements (cutoff + 1) b)
  | .app f a => .app (subst replacements cutoff f) (subst replacements cutoff a)
  | .constant c ui => .constant c ui
  | .inductiveType i ui => .inductiveType i ui
  | .constructor i c ui => .constructor i c ui
  | .caseOf ci p c brs =>
      .caseOf ci
        { p with parameters := p.parameters.map (fun a => subst replacements cutoff a),
                 returnType := subst replacements (p.context.length + cutoff) p.returnType }
        (subst replacements cutoff c)
        (brs.map fun b =>
          { b with body := subst replacements (b.context.length + cutoff) b.body })
  | .projection p c => .projection p (subst replacements cutoff c)
  | .fix ds i =>
      .fix (ds.map fun d => { d with
        type := subst replacements cutoff d.type
        body := subst replacements (ds.length + cutoff) d.body }) i
  | .cofix ds i =>
      .cofix (ds.map fun d => { d with
        type := subst replacements cutoff d.type
        body := subst replacements (ds.length + cutoff) d.body }) i

termination_by t => sizeOf t
decreasing_by
  all_goals simp_wf
  all_goals try omega
  all_goals
    first
    | have h := List.sizeOf_lt_of_mem (by assumption)
      try cases p
      try cases b
      try cases d
      simp_all only [Predicate.mk.sizeOf_spec, Branch.mk.sizeOf_spec, FixDef.mk.sizeOf_spec]
      omega
    | cases p
      simp only [Predicate.mk.sizeOf_spec]
      omega

end Term

end Silmaril.Logic.TypeTheory.CIC
