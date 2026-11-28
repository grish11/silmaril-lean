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

inductive Fragment where
  | core | collections
  deriving DecidableEq

inductive BinderMap where
  | image | function
  deriving Repr

/-- The additional denotations required for the collection fragment. -/
structure CollectionOperations (V : Type u) extends DataOperations V where
  function : V → (V → V) → V
  record : List (String × V) → V
  functionSet : V → V → V
  recordSet : List (String × V) → V
  domain : V → V
  apply : V → V → V
  tuple : List V → V
  /-- The inverse of `tuple` on tuples with the specified length. -/
  untuple : Nat → V → Option (List V)
  /-- A flat product of set operands, with one tuple coordinate per operand. -/
  product : List V → Option V
  /-- An invalid product reports the original bounds, once per source group. -/
  invalidBounds : BinderMap → List V → V
  string : String → V
  /-- Each clause receives the old leaf of the preceding result at its own path. -/
  except : V → List (List V × (V → V)) → V

/-- Core terms use the original operations. Collection terms require a full
collection adapter. -/
abbrev Operations (V : Type u) : Fragment → Type u
  | .core => DataOperations V
  | .collections => CollectionOperations V

abbrev Operations.base {V : Type u} {fragment : Fragment} (ops : Operations V fragment) :
    DataOperations V :=
  match fragment with
  | .core => ops
  | .collections => ops.toDataOperations

def Operations.collection {V : Type u} {fragment : Fragment} (ops : Operations V fragment)
    (enabled : fragment = .collections) : CollectionOperations V :=
  cast (congrArg (Operations V) enabled) ops

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

inductive BinderPattern where
  | name (slot : Nat)
  | tuple (slots : List Nat)
  deriving Repr

def BinderPattern.slots : BinderPattern → List Nat
  | .name slot => [slot]
  | .tuple slots => slots

inductive Bounded where
  | quant (kind : Surface.Quantifier)
  | filter
  | map (kind : BinderMap)
  deriving Repr

/-- Expanded data syntax. A witness slot is fresh at each binder expansion.
The external node carries the admitted declaration identity and actual arity. -/
inductive Term (signature : ExternalSignature) (fragment : Fragment := .core) where
  | rigid (id : BindingId)
  | flexible (id : BindingId)
  | witness (slot : Nat)
  | prime (site : Site) (operand : Term signature fragment)
  | numeral (value : Nat)
  | boolean (value : Bool)
  | booleanSet
  | eq (negated : Bool) (left right : Term signature fragment)
  | mem (negated : Bool) (element set : Term signature fragment)
  | not (arg : Term signature fragment)
  | logic (op : Logic) (left right : Term signature fragment)
  | junction (kind : Surface.Junction) (args : List (Term signature fragment))
  | ite (condition yes no : Term signature fragment)
  | enum (items : List (Term signature fragment))
  | filter (slot : Nat) (bound body : Term signature fragment)
  | image (slot : Nat) (bound body : Term signature fragment)
  | quant (kind : Surface.Quantifier) (slot : Nat) (bound : Option (Term signature fragment))
      (body : Term signature fragment)
  | choose (slot : Nat) (bound : Option (Term signature fragment)) (body : Term signature fragment)
  | chooseTuple (enabled : fragment = .collections) (slots : List Nat)
      (bound : Option (Term signature fragment)) (body : Term signature fragment)
  /-- Each group has its own outer-scope domain. Plain names contribute one
  pattern each, and a tuple pattern contributes one possibly structured key. -/
  | bounded (enabled : fragment = .collections) (kind : Bounded)
      (groups : List (List BinderPattern × Term signature fragment)) (body : Term signature fragment)
  | function (enabled : fragment = .collections) (site : Site) (binder : BindingId)
      (slot : Nat) (bound body : Term signature fragment)
  | functionSet (enabled : fragment = .collections) (site : Site)
      (domain range : Term signature fragment)
  | record (enabled : fragment = .collections) (site : Site) (fields : List (String × Term signature fragment))
  | recordSet (enabled : fragment = .collections) (site : Site)
      (fields : List (String × Term signature fragment))
  | graphDomain (enabled : fragment = .collections) (operand : Term signature fragment)
  | index (enabled : fragment = .collections) (fn key : Term signature fragment)
  | tuple (enabled : fragment = .collections) (items : List (Term signature fragment))
  | string (enabled : fragment = .collections) (value : String)
  | except (enabled : fragment = .collections) (base : Term signature fragment)
      (clauses : List (Nat × List (Term signature fragment) × Term signature fragment))
  | oldValue (enabled : fragment = .collections) (slot : Nat)
  | external (id : BindingId) (arity : Nat) (admitted : signature id = some arity)
      (args : List (Term signature fragment))
  deriving Repr

variable {V : Type u} {signature : ExternalSignature} {fragment : Fragment}

/-- Ordinary witnesses stay rigid under prime. Old values are in scope only at
the endpoint of their binding EXCEPT. -/
structure WitnessScope where
  ordinary : List Nat
  oldValues : List Nat := []
  allowFreeOrdinary : Bool := false

def WitnessScope.isFresh (scope : WitnessScope) (slot : Nat) : Bool :=
  !scope.ordinary.contains slot && !scope.oldValues.contains slot

def WitnessScope.binds (scope : WitnessScope) (slots : List Nat) : Bool :=
  !slots.isEmpty && decide slots.Nodup && slots.all scope.isFresh

mutual

def Term.checkScope (term : Term signature fragment) (scope : WitnessScope) : Bool :=
  match term with
  | .rigid _ | .flexible _ | .numeral _ | .boolean _ | .booleanSet | .string .. => true
  | .witness slot => scope.allowFreeOrdinary || scope.ordinary.contains slot
  | .oldValue _ slot => scope.oldValues.contains slot
  | .eq _ l r | .mem _ l r | .logic _ l r | .functionSet _ _ l r | .index _ l r =>
    l.checkScope scope && r.checkScope scope
  | .not arg | .graphDomain _ arg => arg.checkScope scope
  | .prime _ arg => arg.checkScope { scope with oldValues := [] }
  | .ite c y n => c.checkScope scope && y.checkScope scope && n.checkScope scope
  | .junction _ args | .enum args | .tuple _ args => checkArgs args scope
  | .filter slot bound body | .image slot bound body | .function _ _ _ slot bound body =>
    scope.isFresh slot && bound.checkScope scope &&
      body.checkScope { scope with ordinary := slot :: scope.ordinary }
  | .quant _ slot bound body | .choose slot bound body =>
    let domainOk := match bound with
      | none => true
      | some domain => domain.checkScope scope
    scope.isFresh slot && domainOk &&
      body.checkScope { scope with ordinary := slot :: scope.ordinary }
  | .chooseTuple _ slots bound body =>
    let domainOk := match bound with
      | none => true
      | some domain => domain.checkScope scope
    scope.binds slots && domainOk && body.checkScope { scope with ordinary := slots ++ scope.ordinary }
  | .bounded _ kind groups body =>
    let slots := groups.flatMap fun (patterns, _) => patterns.flatMap BinderPattern.slots
    let shapeOk := match kind with
      | .filter => match groups with | [([_], _)] => true | _ => false
      | _ => true
    shapeOk && scope.binds slots && checkBounds groups scope &&
      body.checkScope { scope with ordinary := slots ++ scope.ordinary }
  | .external _ arity _ args => args.length == arity && checkArgs args scope
  | .record _ _ fields | .recordSet _ _ fields => checkFields fields scope
  | .except _ base clauses => !clauses.isEmpty && base.checkScope scope && checkClauses clauses scope
termination_by structural term

def Term.checkBounds (groups : List (List BinderPattern × Term signature fragment))
    (scope : WitnessScope) : Bool :=
  match groups with
  | [] => true
  | (patterns, domain) :: rest =>
    !patterns.isEmpty && patterns.all (fun p => !p.slots.isEmpty) && domain.checkScope scope &&
      checkBounds rest scope
termination_by structural groups

def Term.checkArgs (args : List (Term signature fragment)) (scope : WitnessScope) : Bool :=
  match args with
  | [] => true
  | arg :: rest => arg.checkScope scope && checkArgs rest scope
termination_by structural args

def Term.checkFields (fields : List (String × Term signature fragment))
    (scope : WitnessScope) : Bool :=
  match fields with
  | [] => true
  | (name, value) :: rest =>
    !rest.any (fun field => field.1 == name) && value.checkScope scope && checkFields rest scope
termination_by structural fields

def Term.checkClauses
    (clauses : List (Nat × List (Term signature fragment) × Term signature fragment))
    (scope : WitnessScope) : Bool :=
  match clauses with
  | [] => true
  | (slot, keys, body) :: rest =>
    scope.isFresh slot && !keys.isEmpty && checkArgs keys scope &&
      body.checkScope { scope with oldValues := slot :: scope.oldValues } &&
      checkClauses rest scope
termination_by structural clauses

end

/-- Check the expanded witness scopes and external argument counts. -/
def Term.isWellFormed (term : Term signature fragment) (scope : List Nat) : Bool :=
  term.checkScope { ordinary := scope }

def Term.argsWellFormed (args : List (Term signature fragment)) (scope : List Nat) : Bool :=
  checkArgs args { ordinary := scope }

def Term.fieldsWellFormed (fields : List (String × Term signature fragment))
    (scope : List Nat) : Bool :=
  checkFields fields { ordinary := scope }

/-- Test an expanded prime operand with ordinary witnesses left in scope.
An old value must be bound by an EXCEPT inside the operand. -/
def Term.validPrimeOperand (term : Term signature fragment) : Bool :=
  term.checkScope { ordinary := [], allowFreeOrdinary := true }

mutual

/-- Find a prime retained after expanding lexical operators and actuals. -/
def Term.firstPrime (term : Term signature fragment) : Option Site :=
  match term with
  | .prime site _ => some site
  | .rigid _ | .flexible _ | .witness _ | .numeral _ | .boolean _ | .booleanSet
  | .oldValue .. | .string .. => none
  | .eq _ l r | .mem _ l r | .logic _ l r | .functionSet _ _ l r | .index _ l r =>
    l.firstPrime.or r.firstPrime
  | .not arg | .graphDomain _ arg => arg.firstPrime
  | .ite c y n => c.firstPrime.or (y.firstPrime.or n.firstPrime)
  | .junction _ args | .enum args | .tuple _ args | .external _ _ _ args => firstPrimeIn args
  | .filter _ bound body | .image _ bound body | .function _ _ _ _ bound body =>
    bound.firstPrime.or body.firstPrime
  | .quant _ _ none body | .choose _ none body | .chooseTuple _ _ none body => body.firstPrime
  | .quant _ _ (some bound) body | .choose _ (some bound) body | .chooseTuple _ _ (some bound) body =>
    bound.firstPrime.or body.firstPrime
  | .bounded _ _ groups body => (firstPrimeInBounds groups).or body.firstPrime
  | .record _ _ fields | .recordSet _ _ fields => firstPrimeInFields fields
  | .except _ base clauses => base.firstPrime.or (firstPrimeInClauses clauses)
termination_by structural term

def Term.firstPrimeInBounds (groups : List (List BinderPattern × Term signature fragment)) : Option Site :=
  match groups with
  | [] => none
  | (_, domain) :: rest => domain.firstPrime.or (firstPrimeInBounds rest)
termination_by structural groups

def Term.firstPrimeIn (args : List (Term signature fragment)) : Option Site :=
  match args with
  | [] => none
  | arg :: rest => arg.firstPrime.or (firstPrimeIn rest)
termination_by structural args

def Term.firstPrimeInFields (fields : List (String × Term signature fragment)) : Option Site :=
  match fields with
  | [] => none
  | (_, value) :: rest => value.firstPrime.or (firstPrimeInFields rest)
termination_by structural fields

def Term.firstPrimeInClauses
    (clauses : List (Nat × List (Term signature fragment) × Term signature fragment)) : Option Site :=
  match clauses with
  | [] => none
  | (_, keys, body) :: rest => (firstPrimeIn keys).or (body.firstPrime.or (firstPrimeInClauses rest))
termination_by structural clauses

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

/-- Assign tuple components to the corresponding witness slots in source order. -/
def withWitnesses (witnesses : Nat → V) (slots : List Nat) (values : List V) : Nat → V :=
  (slots.zip values).foldl (fun env (slot, value) => withWitness env slot value) witnesses

noncomputable def BinderPattern.bind (ops : CollectionOperations V) (pattern : BinderPattern)
    (witnesses : Nat → V) (key : V) : Option (Nat → V) :=
  match pattern with
  | .name slot => some (withWitness witnesses slot key)
  | .tuple slots => (ops.untuple slots.length key).map (withWitnesses witnesses slots)

/-- Images and function bodies use the projections of `CHOOSE z : FALSE`
when the value bound to a tuple pattern has the wrong shape. -/
noncomputable def BinderPattern.bindTotal (ops : CollectionOperations V) (pattern : BinderPattern)
    (witnesses : Nat → V) (key : V) : Nat → V :=
  match pattern with
  | .name slot => withWitness witnesses slot key
  | .tuple slots =>
    let values := (ops.untuple slots.length key).getD
      ((List.range slots.length).map fun i => ops.apply ops.choice.noWitness (ops.numeral (i + 1)))
    withWitnesses witnesses slots values

def Bounded.axes (groups : List (List BinderPattern × V)) : List (BinderPattern × V) :=
  groups.flatMap fun (patterns, domain) => patterns.map (·, domain)

noncomputable def Bounded.quantify (ops : CollectionOperations V) (kind : Surface.Quantifier)
    (predicate : (Nat → V) → Prop) : List (BinderPattern × V) → (Nat → V) → Prop
  | [], witnesses => predicate witnesses
  | (pattern, domain) :: rest, witnesses =>
    match kind with
    | .exists => ∃ x env, ops.mem x domain ∧ pattern.bind ops witnesses x = some env ∧
        quantify ops kind predicate rest env
    | .forall => ∀ x env, ops.mem x domain → pattern.bind ops witnesses x = some env →
        quantify ops kind predicate rest env

noncomputable def BinderMap.eval (kind : BinderMap) (ops : CollectionOperations V)
    (groups : List (List BinderPattern × V)) (witnesses : Nat → V) (body : (Nat → V) → V) : V :=
  let construct := match kind with | .image => ops.image | .function => ops.function
  match Bounded.axes groups with
  | [(pattern, domain)] => construct domain (fun x => body (pattern.bindTotal ops witnesses x))
  | axes =>
    match ops.product (axes.map Prod.snd) with
    | none => ops.invalidBounds kind (groups.map Prod.snd)
    | some domain => construct domain fun key =>
      match ops.untuple axes.length key with
      | none => ops.enum []
      | some keys =>
        body ((axes.map Prod.fst |>.zip keys).foldl
          (fun env (pattern, x) => pattern.bindTotal ops env x) witnesses)

open Classical

mutual

/-- Evaluate expanded syntax using a source valuation and a target flexible map.
The default target is the source map, as used for single-state evaluation. -/
noncomputable def Term.eval (ops : Operations V fragment) (B : Booleans V)
    (external : ExternalInterpretation V signature) (valuation : Valuation V)
    (term : Term signature fragment) (witnesses : Nat → V)
    (target : BindingId → V := valuation.flexible) : V :=
  let truth := fun negated (p : Prop) => B.ofProp (if negated then ¬p else p)
  let base := Operations.base ops
  match term with
  | .rigid id => valuation.rigid id
  | .flexible id => valuation.flexible id
  | .witness slot | .oldValue _ slot => witnesses slot
  | .prime _ operand =>
    eval ops B external { valuation with flexible := target } operand witnesses target
  | .numeral value => base.numeral value
  | .boolean value => if value then B.trueValue else B.falseValue
  | .booleanSet => base.enum [B.trueValue, B.falseValue]
  | .eq negated left right =>
    let l := eval ops B external valuation left witnesses target
    let r := eval ops B external valuation right witnesses target
    truth negated (l = r)
  | .mem negated element set =>
    truth negated (base.mem (eval ops B external valuation element witnesses target)
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
  | .enum items => base.enum (evalList ops B external valuation items witnesses target)
  | .filter slot bound body =>
    base.sep (eval ops B external valuation bound witnesses target)
      (fun x => B.holds (eval ops B external valuation body (withWitness witnesses slot x) target))
  | .image slot bound body =>
    base.image (eval ops B external valuation bound witnesses target)
      (fun x => eval ops B external valuation body (withWitness witnesses slot x) target)
  | .quant kind slot bound body =>
    let predicate := fun x =>
      B.holds (eval ops B external valuation body (withWitness witnesses slot x) target)
    B.ofProp (match kind, bound with
      | .exists, none => ∃ x, predicate x
      | .forall, none => ∀ x, predicate x
      | .exists, some domain =>
        let set := eval ops B external valuation domain witnesses target
        ∃ x, base.mem x set ∧ predicate x
      | .forall, some domain =>
        let set := eval ops B external valuation domain witnesses target
        ∀ x, base.mem x set → predicate x)
  | .choose slot bound body =>
    let predicate := fun x =>
      B.holds (eval ops B external valuation body (withWitness witnesses slot x) target)
    match bound with
    | none => base.choice.choose predicate
    | some domain =>
      let set := eval ops B external valuation domain witnesses target
      base.choice.choose (fun x => base.mem x set ∧ predicate x)
  | .chooseTuple enabled slots bound body =>
    let collection := Operations.collection ops enabled
    let inDomain := match bound with
      | none => fun _ => True
      | some t => fun x => base.mem x (eval ops B external valuation t witnesses target)
    base.choice.choose fun x =>
      inDomain x ∧ ∃ env, (BinderPattern.tuple slots).bind collection witnesses x = some env ∧
        B.holds (eval ops B external valuation body env target)
  | .bounded enabled kind groups body =>
    let collection := Operations.collection ops enabled
    let domains := evalBounds ops B external valuation groups witnesses target
    let value := fun env => eval ops B external valuation body env target
    match kind with
    | .quant quantifier => B.ofProp (Bounded.quantify collection quantifier (fun env => B.holds (value env))
        (Bounded.axes domains) witnesses)
    | .filter =>
      match domains with
      | [([pattern], domain)] => base.sep domain fun x =>
        ∃ env, pattern.bind collection witnesses x = some env ∧ B.holds (value env)
      | _ => base.enum []
    | .map mode => mode.eval collection domains witnesses value
  | .function enabled _ _ slot bound body =>
    (Operations.collection ops enabled).function (eval ops B external valuation bound witnesses target)
      (fun x => eval ops B external valuation body (withWitness witnesses slot x) target)
  | .functionSet enabled _ domain range =>
    (Operations.collection ops enabled).functionSet (eval ops B external valuation domain witnesses target)
      (eval ops B external valuation range witnesses target)
  | .record enabled _ fields =>
    (Operations.collection ops enabled).record (evalFields ops B external valuation fields witnesses target)
  | .recordSet enabled _ fields =>
    (Operations.collection ops enabled).recordSet (evalFields ops B external valuation fields witnesses target)
  | .graphDomain enabled operand =>
    (Operations.collection ops enabled).domain (eval ops B external valuation operand witnesses target)
  | .index enabled fn key =>
    (Operations.collection ops enabled).apply (eval ops B external valuation fn witnesses target)
      (eval ops B external valuation key witnesses target)
  | .tuple enabled items =>
    (Operations.collection ops enabled).tuple (evalList ops B external valuation items witnesses target)
  | .string enabled value => (Operations.collection ops enabled).string value
  | .except enabled root clauses =>
    (Operations.collection ops enabled).except (eval ops B external valuation root witnesses target)
      (evalClauses ops B external valuation clauses witnesses target)
  | .external id arity admitted args =>
    (external id arity admitted).apply (evalList ops B external valuation args witnesses target)
termination_by structural term

noncomputable def Term.evalBounds (ops : Operations V fragment) (B : Booleans V)
    (external : ExternalInterpretation V signature) (valuation : Valuation V)
    (groups : List (List BinderPattern × Term signature fragment)) (witnesses : Nat → V)
    (target : BindingId → V) : List (List BinderPattern × V) :=
  match groups with
  | [] => []
  | (patterns, domain) :: rest =>
    (patterns, eval ops B external valuation domain witnesses target) ::
      evalBounds ops B external valuation rest witnesses target
termination_by structural groups

noncomputable def Term.evalList (ops : Operations V fragment) (B : Booleans V)
    (external : ExternalInterpretation V signature) (valuation : Valuation V)
    (terms : List (Term signature fragment)) (witnesses : Nat → V)
    (target : BindingId → V := valuation.flexible) : List V :=
  match terms with
  | [] => []
  | item :: rest =>
    eval ops B external valuation item witnesses target ::
      evalList ops B external valuation rest witnesses target
termination_by structural terms

noncomputable def Term.evalFields (ops : Operations V fragment) (B : Booleans V)
    (external : ExternalInterpretation V signature) (valuation : Valuation V)
    (fields : List (String × Term signature fragment)) (witnesses : Nat → V)
    (target : BindingId → V) : List (String × V) :=
  match fields with
  | [] => []
  | (name, value) :: rest =>
    (name, eval ops B external valuation value witnesses target) ::
      evalFields ops B external valuation rest witnesses target
termination_by structural fields

noncomputable def Term.evalClauses (ops : Operations V fragment) (B : Booleans V)
    (external : ExternalInterpretation V signature) (valuation : Valuation V)
    (clauses : List (Nat × List (Term signature fragment) × Term signature fragment))
    (witnesses : Nat → V) (target : BindingId → V) : List (List V × (V → V)) :=
  match clauses with
  | [] => []
  | (slot, keys, body) :: rest =>
    (evalList ops B external valuation keys witnesses target,
      fun old => eval ops B external valuation body (withWitness witnesses slot old) target) ::
    evalClauses ops B external valuation rest witnesses target
termination_by structural clauses

end

end
end Silmaril.Logic.Temporal.TLA.DataElab
