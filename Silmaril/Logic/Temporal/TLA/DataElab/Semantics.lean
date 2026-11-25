module

public import Silmaril.Logic.Temporal.TLA.Data.Defs
public import Silmaril.Logic.Temporal.TLA.Resolution.Defs

/-! The expanded data expressions and their mathematical interpretation. -/

namespace Silmaril.Logic.Temporal.TLA.DataElab

@[expose] public section

open Resolution

universe u

/-- The admitted external declaration identities and their expression arities. -/
abbrev ExternalSignature := BindingId → Option Nat

/-- An interpretation of an external declaration with a caller-stated contract. -/
structure Primitive (V : Type u) (arity : Nat) where
  apply : List V → V
  spec : List V → V → Prop
  sound : ∀ args, args.length = arity → spec args (apply args)

abbrev ExternalInterpretation (V : Type u) (signature : ExternalSignature) :=
  (id : BindingId) → (arity : Nat) → signature id = some arity → Primitive V arity

/-- Operations required by data evaluation. Adapters own the laws for these
operations, including the results on values outside their set representation. -/
structure DataOperations (V : Type u) where
  numeral : Nat → V
  mem : V → V → Prop
  enum : List V → V
  sep : V → (V → Prop) → V
  image : V → (V → V) → V
  choice : Data.ChoicePolicy V

/-- Use the pure-set interpretation, its choice policy and a caller-supplied numeral encoding. -/
def DataOperations.ofModel {V : Type u} (model : Data.Model V) (numeral : Nat → V) :
    DataOperations V where
  numeral := numeral
  mem := model.mem
  enum := model.enum
  sep := model.sep
  image := model.image
  choice := model.choice

inductive Logic where
  | and | or | implies | equiv
  deriving DecidableEq, Repr

inductive BooleanContext where
  | negation
  | binary (op : Logic)
  | junction (kind : Surface.Junction)
  | conditional
  deriving Repr

/-- Boolean values and the caller's policies for non-Boolean inputs. Binder
predicates use `holds`. Logical operators and IF use `invalid` when
the Boolean inputs do not determine the result. -/
structure Booleans (V : Type u) where
  trueValue : V
  falseValue : V
  holds : V → Prop
  holds_true : holds trueValue
  not_holds_false : ¬ holds falseValue
  invalid : BooleanContext → List V → V

namespace Booleans

variable {V : Type u}

open Classical in
noncomputable def ofProp (B : Booleans V) (p : Prop) : V :=
  if p then B.trueValue else B.falseValue

@[simp] theorem ofProp_true (B : Booleans V) : B.ofProp True = B.trueValue := ite_eq_left trivial

@[simp] theorem ofProp_false (B : Booleans V) : B.ofProp False = B.falseValue := ite_eq_right not_false

def IsBoolean (B : Booleans V) (value : V) : Prop :=
  value = B.trueValue ∨ value = B.falseValue

theorem holds_ofProp (B : Booleans V) (p : Prop) : B.holds (B.ofProp p) ↔ p := by
  classical
  by_cases p <;> simp_all [ofProp, B.holds_true, B.not_holds_false]

end Booleans

/-- Rigid constants use the same assignment at every state. The flexible
assignment supplies one state's values for variable declarations. -/
structure Valuation (V : Type u) where
  rigid : BindingId → V
  flexible : BindingId → V

/-- Expanded data syntax. A witness slot is fresh at each binder expansion.
The external node carries the admitted declaration identity and actual arity. -/
inductive Term (signature : ExternalSignature) where
  | rigid (id : BindingId)
  | flexible (id : BindingId)
  | witness (slot : Nat)
  | prime (site : Site) (operand : Term signature)
  | numeral (value : Nat)
  | boolean (value : Bool)
  | booleanSet
  | eq (negated : Bool) (left right : Term signature)
  | mem (negated : Bool) (element set : Term signature)
  | not (arg : Term signature)
  | logic (op : Logic) (left right : Term signature)
  | junction (kind : Surface.Junction) (args : List (Term signature))
  | ite (condition yes no : Term signature)
  | enum (items : List (Term signature))
  | filter (slot : Nat) (bound body : Term signature)
  | image (slot : Nat) (bound body : Term signature)
  | quant (kind : Surface.Quantifier) (slot : Nat) (bound : Option (Term signature))
      (body : Term signature)
  | choose (slot : Nat) (bound : Option (Term signature)) (body : Term signature)
  | external (id : BindingId) (arity : Nat) (admitted : signature id = some arity)
      (args : List (Term signature))
  deriving Repr

variable {V : Type u} {signature : ExternalSignature}

mutual

/-- Check the expanded witness scopes and external argument counts. -/
def Term.isWellFormed (term : Term signature) (scope : List Nat) : Bool :=
  match term with
  | .rigid _ | .flexible _ | .numeral _ | .boolean _ | .booleanSet => true
  | .witness slot => scope.contains slot
  | .eq _ l r | .mem _ l r | .logic _ l r => l.isWellFormed scope && r.isWellFormed scope
  | .not arg | .prime _ arg => arg.isWellFormed scope
  | .ite c y n => c.isWellFormed scope && y.isWellFormed scope && n.isWellFormed scope
  | .junction _ args | .enum args => argsWellFormed args scope
  | .filter slot bound body | .image slot bound body =>
    !scope.contains slot && bound.isWellFormed scope && body.isWellFormed (slot :: scope)
  | .quant _ slot bound body | .choose slot bound body =>
    let domainOk := match bound with
      | none => true
      | some domain => domain.isWellFormed scope
    !scope.contains slot && domainOk && body.isWellFormed (slot :: scope)
  | .external _ arity _ args => args.length == arity && argsWellFormed args scope
termination_by structural term

def Term.argsWellFormed (args : List (Term signature)) (scope : List Nat) : Bool :=
  match args with
  | [] => true
  | arg :: rest => arg.isWellFormed scope && argsWellFormed rest scope
termination_by structural args

end

mutual

/-- Find a prime retained after expanding lexical operators and actuals. -/
def Term.firstPrime (term : Term signature) : Option Site :=
  match term with
  | .prime site _ => some site
  | .rigid _ | .flexible _ | .witness _ | .numeral _ | .boolean _ | .booleanSet => none
  | .eq _ l r | .mem _ l r | .logic _ l r => l.firstPrime.or r.firstPrime
  | .not arg => arg.firstPrime
  | .ite c y n => c.firstPrime.or (y.firstPrime.or n.firstPrime)
  | .junction _ args | .enum args | .external _ _ _ args => firstPrimeIn args
  | .filter _ bound body | .image _ bound body => bound.firstPrime.or body.firstPrime
  | .quant _ _ none body | .choose _ none body => body.firstPrime
  | .quant _ _ (some bound) body | .choose _ (some bound) body =>
    bound.firstPrime.or body.firstPrime
termination_by structural term

def Term.firstPrimeIn (args : List (Term signature)) : Option Site :=
  match args with
  | [] => none
  | arg :: rest => arg.firstPrime.or (firstPrimeIn rest)
termination_by structural args

end

def Logic.holds (op : Logic) (p q : Prop) : Prop :=
  match op with
  | .and => p ∧ q
  | .or => p ∨ q
  | .implies => p → q
  | .equiv => p ↔ q

open Classical in
/-- Boolean operands and absorbing values determine the usual result.
The interpretation supplies the value in the other cases. -/
noncomputable def Logic.eval (op : Logic) (B : Booleans V) (left right : V) : V :=
  let general :=
    if B.IsBoolean left ∧ B.IsBoolean right then B.ofProp (op.holds (B.holds left) (B.holds right))
    else B.invalid (.binary op) [left, right]
  match op with
  | .and => if left = B.falseValue ∨ right = B.falseValue then B.falseValue else general
  | .or => if left = B.trueValue ∨ right = B.trueValue then B.trueValue else general
  | .implies => if left = B.falseValue ∨ right = B.trueValue then B.trueValue else general
  | .equiv => general

/-- Assign a value to a witness slot while evaluating its scope. -/
def withWitness (witnesses : Nat → V) (slot : Nat) (value : V) : Nat → V :=
  fun i => if i = slot then value else witnesses i

open Classical

mutual

/-- Evaluate expanded syntax using a source valuation and a target flexible map.
The default target is the source map, as used for single-state evaluation. -/
noncomputable def Term.eval (ops : DataOperations V) (B : Booleans V)
    (external : ExternalInterpretation V signature) (valuation : Valuation V)
    (term : Term signature) (witnesses : Nat → V)
    (target : BindingId → V := valuation.flexible) : V :=
  let truth := fun negated (p : Prop) => B.ofProp (if negated then ¬p else p)
  match term with
  | .rigid id => valuation.rigid id
  | .flexible id => valuation.flexible id
  | .witness slot => witnesses slot
  | .prime _ operand =>
    eval ops B external { valuation with flexible := target } operand witnesses target
  | .numeral value => ops.numeral value
  | .boolean value => if value then B.trueValue else B.falseValue
  | .booleanSet => ops.enum [B.trueValue, B.falseValue]
  | .eq negated left right =>
    let l := eval ops B external valuation left witnesses target
    let r := eval ops B external valuation right witnesses target
    truth negated (l = r)
  | .mem negated element set =>
    truth negated (ops.mem (eval ops B external valuation element witnesses target)
      (eval ops B external valuation set witnesses target))
  | .not arg =>
    let value := eval ops B external valuation arg witnesses target
    if B.IsBoolean value then B.ofProp (¬B.holds value) else B.invalid .negation [value]
  | .logic op left right =>
    let l := eval ops B external valuation left witnesses target
    let r := eval ops B external valuation right witnesses target
    op.eval B l r
  | .junction kind args =>
    let values := evalList ops B external valuation args witnesses target
    let (absorbing, identity) := match kind with
      | .conjunction => (B.falseValue, B.trueValue)
      | .disjunction => (B.trueValue, B.falseValue)
    if absorbing ∈ values then absorbing
    else if ∀ value ∈ values, B.IsBoolean value then identity
    else B.invalid (.junction kind) values
  | .ite condition yes no =>
    let value := eval ops B external valuation condition witnesses target
    let consequent := eval ops B external valuation yes witnesses target
    let alternative := eval ops B external valuation no witnesses target
    if B.IsBoolean value then
      if B.holds value then consequent else alternative
    else B.invalid .conditional [value, consequent, alternative]
  | .enum items => ops.enum (evalList ops B external valuation items witnesses target)
  | .filter slot bound body =>
    ops.sep (eval ops B external valuation bound witnesses target)
      (fun x => B.holds (eval ops B external valuation body (withWitness witnesses slot x) target))
  | .image slot bound body =>
    ops.image (eval ops B external valuation bound witnesses target)
      (fun x => eval ops B external valuation body (withWitness witnesses slot x) target)
  | .quant kind slot bound body =>
    let predicate := fun x =>
      B.holds (eval ops B external valuation body (withWitness witnesses slot x) target)
    B.ofProp (match kind, bound with
      | .exists, none => ∃ x, predicate x
      | .forall, none => ∀ x, predicate x
      | .exists, some domain =>
        let set := eval ops B external valuation domain witnesses target
        ∃ x, ops.mem x set ∧ predicate x
      | .forall, some domain =>
        let set := eval ops B external valuation domain witnesses target
        ∀ x, ops.mem x set → predicate x)
  | .choose slot bound body =>
    let predicate := fun x =>
      B.holds (eval ops B external valuation body (withWitness witnesses slot x) target)
    match bound with
    | none => ops.choice.choose predicate
    | some domain =>
      let set := eval ops B external valuation domain witnesses target
      ops.choice.choose (fun x => ops.mem x set ∧ predicate x)
  | .external id arity admitted args =>
    (external id arity admitted).apply (evalList ops B external valuation args witnesses target)
termination_by structural term

noncomputable def Term.evalList (ops : DataOperations V) (B : Booleans V)
    (external : ExternalInterpretation V signature) (valuation : Valuation V)
    (terms : List (Term signature)) (witnesses : Nat → V)
    (target : BindingId → V := valuation.flexible) : List V :=
  match terms with
  | [] => []
  | item :: rest =>
    eval ops B external valuation item witnesses target ::
      evalList ops B external valuation rest witnesses target
termination_by structural terms

end

end
end Silmaril.Logic.Temporal.TLA.DataElab
