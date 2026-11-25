module

/-!
# Named TLA+ surface syntax

These trees retain source binding, application and proof structure. Names are
unresolved. Source locations and diagnostics belong to the producer or consumer
of a tree. See `docs/projects/tla.md` for the pinned grammar and coverage.
-/

public section

namespace Silmaril.Logic.Temporal.TLA.Surface

abbrev Ident := String

inductive Literal where
  | natural (value : Nat)
  /-- The fractional digits include any leading or trailing zeroes. -/
  | decimal (whole : Nat) (fractionalDigits : String)
  | string (value : String)
  deriving Repr

inductive PrefixOp where
  | negation | minus | enabled | unchanged | always | eventually
  | subset | union | domain
  | symbol (spelling : String)
  deriving Repr

inductive InfixOp where
  | compose | leadsTo | guarantees
  | symbol (spelling : String)
  deriving Repr

inductive PostfixOp where
  | prime
  | symbol (spelling : String)
  deriving Repr

inductive Symbol where
  | prefix (op : PrefixOp)
  | infix (op : InfixOp)
  | postfix (op : PostfixOp)
  deriving Repr

inductive OperatorName where
  | ident (name : Ident)
  | symbolic (op : Symbol)
  deriving Repr

/-- An operator signature with anonymous argument slots, as in `F(_, _)` or `_ + _`. -/
inductive OperatorDecl where
  | ident (name : Ident) (arity : Nat)
  | symbolic (op : Symbol)
  deriving Repr

/-- The left-hand side of an operator definition. Identifier forms can bind operators. -/
inductive OperatorHead where
  | ident (name : Ident) (parameters : List OperatorDecl)
  | prefix (op : PrefixOp) (arg : Ident)
  | infix (left : Ident) (op : InfixOp) (right : Ident)
  | postfix (arg : Ident) (op : PostfixOp)
  deriving Repr

inductive BoundPattern where
  | ident (name : Ident)
  | tuple (names : List Ident)
  deriving Repr

/-- A shared domain binds either a group of names or one tuple pattern. -/
inductive BoundNames where
  | names (names : List Ident)
  | tuple (names : List Ident)
  deriving Repr

inductive Quantifier where
  | exists | forall
  deriving Repr

inductive Junction where
  | conjunction | disjunction
  deriving Repr

inductive ActionBracket where
  | square | angle
  deriving Repr

inductive Fairness where
  | weak | strong
  deriving Repr

inductive StructuralSelector where
  | operand (index : Nat) -- !n, with source numbering
  | left        -- !<<
  | right       -- !>>
  | body        -- !:
  | allBindings -- !@
  deriving Repr

inductive StepRefLevel where
  | explicit (level : Nat)
  | current
  deriving Repr

structure StepRef where
  level : StepRefLevel
  name : Ident
  deriving Repr

inductive RefHead where
  | operator (name : OperatorName)
  | step (reference : StepRef)
  deriving Repr

structure Label where
  name : Ident
  parameters : List Ident
  deriving Repr

inductive Visibility where
  | ordinary | local
  deriving Repr

mutual

inductive Expr where
  /-- Each segment of a reference keeps its own parenthesized arguments.
  A named segment may resolve to an instance, operator, or label. -/
  | ref (head : RefHead) (args : List OpArg) (selectors : List Selector)
  | literal (value : Literal)
  | prefix (op : PrefixOp) (arg : Expr)
  | infix (op : InfixOp) (left right : Expr)
  | postfix (op : PostfixOp) (arg : Expr)
  /-- A flat chain of Cartesian product factors. A grouped product is a nested factor. -/
  | cartesian (factors : List Expr)
  | junction (kind : Junction) (items : List Expr)
  | ifThenElse (condition consequent alternative : Expr)
  | cases (arms : List CaseArm) (other : Option Expr)
  | letIn (declarations : List LetDecl) (body : Expr)
  | rigidQuant (quantifier : Quantifier) (binders : RigidBinders) (body : Expr)
  | temporalQuant (quantifier : Quantifier) (names : List Ident) (body : Expr)
  | choose (pattern : BoundPattern) (domain : Option Expr) (predicate : Expr)
  | setEnum (elements : List Expr)
  | setFilter (pattern : BoundPattern) (domain predicate : Expr)
  | setMap (body : Expr) (bounds : List Bound)
  | function (bounds : List Bound) (body : Expr)
  | functionSet (domain range : Expr)
  | index (fn : Expr) (args : List Expr)
  | tuple (elements : List Expr)
  | record (fields : List Field)
  | recordSet (fields : List Field)
  | field (record : Expr) (name : Ident)
  | except (base : Expr) (updates : List Update)
  | oldValue
  | action (kind : ActionBracket) (body subscript : Expr)
  | fairness (kind : Fairness) (subscript action : Expr)
  | labeled (label : Label) (body : Expr)
  deriving Repr

inductive OpArg where
  /-- Bare or qualified named arguments retain their expression shape until arity resolution. -/
  | expr (value : Expr)
  | symbolic (op : Symbol)
  | lambda (parameters : List Ident) (body : Expr)
  deriving Repr

inductive Selector where
  | named (name : OperatorName) (args : List OpArg)
  | arguments (args : List OpArg)
  | structural (selector : StructuralSelector)
  deriving Repr

structure Bound where
  names : BoundNames
  domain : Expr
  deriving Repr

inductive RigidBinders where
  | unbounded (names : List Ident)
  | bounded (groups : List Bound)
  deriving Repr

structure CaseArm where
  condition : Expr
  result : Expr
  deriving Repr

/-- The enclosing record form determines whether the expression is a value or a set. -/
structure Field where
  name : Ident
  value : Expr
  deriving Repr

inductive UpdateComponent where
  | field (name : Ident)
  | index (args : List Expr)
  deriving Repr

structure Update where
  path : List UpdateComponent
  value : Expr
  deriving Repr

structure Substitution where
  target : OperatorName
  replacement : OpArg
  deriving Repr

structure Instantiation where
  moduleName : Ident
  substitutions : List Substitution
  deriving Repr

inductive Definition where
  | operator (visibility : Visibility) (head : OperatorHead) (body : Expr)
  | function (visibility : Visibility) (name : Ident) (bounds : List Bound) (body : Expr)
  | namedInstance (visibility : Visibility) (name : Ident) (parameters : List OperatorDecl)
      (instanceBody : Instantiation)
  deriving Repr

inductive LetDecl where
  | definition (value : Definition)
  | recursive (operators : List OperatorDecl)
  deriving Repr

end

inductive SymbolLevel where
  | constant | state | action | temporal
  deriving Repr

inductive AssumeProveMode where
  | plain | boxed
  deriving Repr

mutual

inductive Statement where
  | expr (value : Expr)
  /-- Keep the two keyword modes distinct so a validator can diagnose a mismatch. -/
  | assumeProve (assumeMode : AssumeProveMode) (hypotheses : List Hypothesis)
      (proveMode : AssumeProveMode) (goal : Expr)
  | labeled (name : Ident) (statement : Statement)
  deriving Repr

inductive Hypothesis where
  | statement (value : Statement)
  | newSymbol (level : SymbolLevel) (declaration : OperatorDecl)
  | newVariable (name : Ident)
  | newBoundConstant (name : Ident) (domain : Expr)
  deriving Repr

end

inductive Citation where
  | expr (value : Expr)
  | moduleName (name : Ident)
  deriving Repr

structure Citations where
  facts : List Citation
  defs : List Citation
  deriving Repr

inductive Directive where
  | use (only : Bool) (citations : Citations)
  | hide (citations : Citations)
  deriving Repr

inductive StepLevel where
  | explicit (level : Nat)
  | current -- <*>
  | next    -- <+>
  deriving Repr

structure StepLabel where
  level : StepLevel
  name : Option Ident
  deriving Repr

mutual

inductive Proof where
  | obvious
  | omitted
  | byFacts (only : Bool) (citations : Citations)
  | steps (steps : List ProofStep) (qedLabel : StepLabel) (qedProof : Option Proof)
  deriving Repr

structure ProofStep where
  label : StepLabel
  body : StepBody
  deriving Repr

inductive StepBody where
  | directive (value : Directive)
  | instantiation (value : Instantiation)
  | define (definitions : List Definition)
  | have (value : Expr)
  | take (binders : RigidBinders)
  | witness (values : List Expr)
  | pick (binders : RigidBinders) (predicate : Expr) (proof : Option Proof)
  | caseOf (condition : Expr) (proof : Option Proof)
  | assert (statement : Statement) (proof : Option Proof)
  | suffices (statement : Statement) (proof : Option Proof)
  deriving Repr

end

structure Theorem where
  name : Option Ident
  statement : Statement
  proof : Option Proof
  deriving Repr

mutual

structure Module where
  name : Ident
  extendsModules : List Ident
  units : List ModuleUnit
  deriving Repr

inductive ModuleUnit where
  | variables (names : List Ident)
  | constants (operators : List OperatorDecl)
  | recursive (operators : List OperatorDecl)
  | definition (value : Definition)
  | instantiation (visibility : Visibility) (value : Instantiation)
  | assumption (name : Option Ident) (body : Expr)
  | theoremDecl (value : Theorem)
  | submodule (value : Module)
  | directive (value : Directive)
  deriving Repr

end

end Silmaril.Logic.Temporal.TLA.Surface
