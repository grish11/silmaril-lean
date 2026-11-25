module

public import Silmaril.Logic.Temporal.TLA.DataElab.Defs
import all Silmaril.Logic.Temporal.TLA.DataElab.Defs
meta import Silmaril.Logic.Temporal.TLA.DataElab.Defs
import Silmaril.Logic.Temporal.TLA.Data.Thms
import Silmaril.Logic.Temporal.TLA.DataElab.Endpoints.Thms
import all Silmaril.Logic.Temporal.TLA.DataElab.Endpoints.Defs
meta import Silmaril.Logic.Temporal.TLA.DataElab.Endpoints.Defs
meta import Silmaril.Logic.Temporal.TLA.Surface.Parser.Defs
public import Lean
public meta import Lean

/-! Parser-to-denotation checks on in-memory modules. -/

namespace Silmaril.Logic.Temporal.TLA.DataElab.Examples

open Resolution

private def baseId : BindingId := .declared ⟨"home", [.unit 0, .member 0]⟩
private def xId : BindingId := .declared ⟨"root", [.unit 0, .member 0]⟩
private meta def wrapId : BindingId := .declared ⟨"prims", [.member 0]⟩

private meta def fixtureSignature : ExternalSignature
  | .declared ⟨"prims", [.member 0]⟩ => some 1
  | _ => none

private meta def homeText := r#"---- MODULE Home ----
CONSTANT Base
LOCAL Keep(z) == {Base, z}
Apply(F(_), y) == LET Run(t) == Keep(F(t)) IN Run(y)
Some(P(_), S) == \E item \in S : P(item)
====
"#

private meta def rootText := r#"---- MODULE Root ----
EXTENDS Home, Prims
VARIABLE x
LOCAL Keep(ignored) == {}
Pool == LET Capture(t) == IF t \in {x} THEN t ELSE Base
            Forward(G(_)) == Apply(G, x)
        IN Forward(Capture)
Data == {Wrap(k) : k \in {w \in Pool : w /= Base}}
Pick == CHOOSE y \in {x} : y = x
Nested == Some(LAMBDA a: Some(LAMBDA b: a /= b, {Base}), {x})
PrimeArg(p) == (p = x)'
PrimeUse == PrimeArg({x})
TupleUse == <<x>>
a \oplus b == a
Symbolic == LET Use(F(_, _)) == F(x, Base) IN Use(⊕)
All == \A a, b \in {x} : a = b
Invalid == IF {} THEN x ELSE Base
Forced == (FALSE /\ {}) = FALSE
ImageFromBase == {y : y \in Base}
Numeral == 12
====
"#

private meta def exampleRegistry (primitiveModule : ModuleId := "prims") :
    Except String CheckedRegistry := do
  let home ← (Surface.Parser.parseModule homeText).mapError reprStr
  let root ← (Surface.Parser.parseModule rootText).mapError reprStr
  (Resolution.resolve [
    ("root", .parsed root [("Home", "home"), ("Prims", primitiveModule)]),
    ("home", .parsed home []),
    (primitiveModule, .signature "Prims" [] [.operator (.ident "Wrap") [.expression]])
  ] "root").mapError reprStr

private meta def find (registry : CheckedRegistry) (name : String) : Except String BindingId := do
  let some binding := (registry.moduleAt "root").bind (·.bindingAt (.ident name))
    | throw ("fixture definition not found: " ++ name)
  return binding.id

private meta def fixture (name : String) : Except String (CheckedExpr fixtureSignature) := do
  let registry ← exampleRegistry
  let id ← find registry name
  (lowerDefinition registry fixtureSignature 40 id).mapError reprStr

private meta def rejects (name : String) (diagnostic : DataElab.Diagnostic)
    (depth : Nat := 40) (signature : ExternalSignature := fixtureSignature)
    (primitiveModule : ModuleId := "prims") : Bool :=
  match exampleRegistry primitiveModule with
  | .error _ => false
  | .ok registry =>
    match find registry name with
    | .error _ => false
    | .ok id =>
      match lowerDefinition registry signature depth id with
      | .error err => err = diagnostic
      | .ok _ => false

#guard rejects "PrimeUse" ⟨⟨"root", [.unit 6, .body]⟩, .primeRequiresLevels⟩
#guard rejects "TupleUse" ⟨⟨"root", [.unit 8, .body]⟩, .unsupported .tuple⟩
#guard rejects "Pool" ⟨⟨"root", [.unit 2, .body]⟩, .expansionLimit⟩ 0
#guard rejects "Data" ⟨⟨"root", [.unit 3, .body, .body]⟩, .primitiveArity wrapId 1 2⟩
  (signature := fun id => if id = wrapId then some 2 else none)
#guard rejects "Data" ⟨⟨"root", [.unit 3, .body, .body]⟩,
    .missingPrimitive (.declared ⟨"other-prims", [.member 0]⟩)⟩
  (primitiveModule := "other-prims")

meta section

open Lean

deriving instance ToExpr for Resolution.Fixity
deriving instance ToExpr for Resolution.Name
deriving instance ToExpr for Step
deriving instance ToExpr for Site
deriving instance ToExpr for BindingId
deriving instance ToExpr for Logic
deriving instance ToExpr for Surface.Junction
deriving instance ToExpr for Surface.Quantifier

-- Only the fixture is staged. The kernel checks the quoted expression, including
-- the admission proof for a primitive. The parser and resolver run during elaboration.
private meta partial def quoteTerm (term : Term fixtureSignature) : Elab.Term.TermElabM Lean.Expr := do
  let sig := mkConst ``fixtureSignature
  let type := mkApp (mkConst ``Term) sig
  let node := fun (ctor : Lean.Name) args => mkAppN (mkApp (mkConst ctor) sig) args
  let list := fun args => do
    let values ← args.mapM quoteTerm
    Meta.mkListLit type values
  let opt := fun bound => match bound with
    | none => pure (mkApp (mkConst ``Option.none [0]) type)
    | some t => return mkApp2 (mkConst ``Option.some [0]) type (← quoteTerm t)
  match term with
  | .rigid id => return node ``Term.rigid #[toExpr id]
  | .flexible id => return node ``Term.flexible #[toExpr id]
  | .witness slot => return node ``Term.witness #[toExpr slot]
  | .prime site operand => return node ``Term.prime #[toExpr site, ← quoteTerm operand]
  | .numeral value => return node ``Term.numeral #[toExpr value]
  | .boolean b => return node ``Term.boolean #[toExpr b]
  | .booleanSet => return node ``Term.booleanSet #[]
  | .eq b l r => return node ``Term.eq #[toExpr b, ← quoteTerm l, ← quoteTerm r]
  | .mem b l r => return node ``Term.mem #[toExpr b, ← quoteTerm l, ← quoteTerm r]
  | .not t => return node ``Term.not #[← quoteTerm t]
  | .logic op l r => return node ``Term.logic #[toExpr op, ← quoteTerm l, ← quoteTerm r]
  | .junction kind args => return node ``Term.junction #[toExpr kind, ← list args]
  | .ite c y n => return node ``Term.ite #[← quoteTerm c, ← quoteTerm y, ← quoteTerm n]
  | .enum args => return node ``Term.enum #[← list args]
  | .filter i s p => return node ``Term.filter #[toExpr i, ← quoteTerm s, ← quoteTerm p]
  | .image i s f => return node ``Term.image #[toExpr i, ← quoteTerm s, ← quoteTerm f]
  | .quant q i s p => return node ``Term.quant #[toExpr q, toExpr i, ← opt s, ← quoteTerm p]
  | .choose i s p => return node ``Term.choose #[toExpr i, ← opt s, ← quoteTerm p]
  | .external id arity _ args =>
    let key := toExpr id
    let expected ← Meta.mkEq (mkApp sig key) (toExpr (some arity))
    let admitted ← Elab.Term.elabTerm (← `(by simp [fixtureSignature])) (some expected)
    return node ``Term.external #[key, toExpr arity, admitted, ← list args]

private meta def emit (name : String) : Elab.Term.TermElabM Lean.Expr := do
  match fixture name with
  | .error message => throwError "{message}"
  | .ok checked =>
    let term ← quoteTerm checked.term
    let valid ← Meta.mkEqRefl (toExpr true)
    return mkApp3 (mkConst ``CheckedExpr.mk) (mkConst ``fixtureSignature) term valid

end

private noncomputable def poolExpr : CheckedExpr fixtureSignature := by_elab emit "Pool"
private noncomputable def dataExpr : CheckedExpr fixtureSignature := by_elab emit "Data"
private noncomputable def pickExpr : CheckedExpr fixtureSignature := by_elab emit "Pick"
private noncomputable def nestedExpr : CheckedExpr fixtureSignature := by_elab emit "Nested"
private noncomputable def symbolicExpr : CheckedExpr fixtureSignature := by_elab emit "Symbolic"
private noncomputable def allExpr : CheckedExpr fixtureSignature := by_elab emit "All"
private noncomputable def invalidExpr : CheckedExpr fixtureSignature := by_elab emit "Invalid"
private noncomputable def forcedExpr : CheckedExpr fixtureSignature := by_elab emit "Forced"
private noncomputable def imageExpr : CheckedExpr fixtureSignature := by_elab emit "ImageFromBase"
private noncomputable def numeralExpr : CheckedExpr fixtureSignature := by_elab emit "Numeral"

universe u
variable {V : Type u} (M : Data.Model V) (numeral : Nat → V) (B : Booleans V) (v : Valuation V)

private def external (ops : DataOperations V) : ExternalInterpretation V fixtureSignature :=
  fun _ _ _ =>
    { apply := ops.enum
      spec := fun args result => result = ops.enum args
      sound := fun _ _ => rfl }

private noncomputable def evaluate (expr : CheckedExpr fixtureSignature) : V :=
  let ops := DataOperations.ofModel M numeral
  expr.eval ops B (external ops) v

private abbrev base := v.rigid baseId
private abbrev x := v.flexible xId

private theorem pool_eq : evaluate M numeral B v poolExpr = M.enum [base v, x v] := by
  classical
  simp [evaluate, CheckedExpr.eval, DataOperations.ofModel, poolExpr, Term.eval, Term.evalList,
    Data.Model.mem_enum, Booleans.IsBoolean, B.holds_true, base, x, baseId, xId]

private theorem data_eq :
    evaluate M numeral B v dataExpr =
      M.image (M.sep (M.enum [base v, x v]) (· ≠ base v)) (fun y => M.enum [y]) := by
  classical
  simp [evaluate, CheckedExpr.eval, DataOperations.ofModel, dataExpr, Term.eval, Term.evalList,
    Data.Model.mem_enum, withWitness, external, Booleans.holds_ofProp, Booleans.IsBoolean,
    B.holds_true, base, x, baseId, xId]

private theorem pick_eq : evaluate M numeral B v pickExpr = x v := by
  have equation : evaluate M numeral B v pickExpr = M.chooseIn (M.enum [x v]) (· = x v) := by
    simp [evaluate, CheckedExpr.eval, DataOperations.ofModel, pickExpr, Term.eval, Term.evalList, withWitness,
      Booleans.holds_ofProp, Data.Model.chooseIn, Data.Model.choose, x, xId]
  rw [equation]
  have witness : M.existsIn (M.enum [x v]) (· = x v) := ⟨x v, by simp, rfl⟩
  exact (M.existsIn_iff_chooseIn.mp witness).2

private theorem nested_iff :
    B.holds (evaluate M numeral B v nestedExpr) ↔ x v ≠ base v := by
  simp [evaluate, CheckedExpr.eval, DataOperations.ofModel, nestedExpr, Term.eval, Term.evalList, withWitness,
    Booleans.holds_ofProp, x, xId, base, baseId]

example : evaluate M numeral B v symbolicExpr = x v := rfl

example : B.holds (evaluate M numeral B v allExpr) := by
  simp [evaluate, CheckedExpr.eval, DataOperations.ofModel, allExpr, Term.eval, Term.evalList, withWitness,
    Booleans.holds_ofProp, B.holds_true]

example (h : ¬ B.IsBoolean M.empty) :
    evaluate M numeral B v invalidExpr = B.invalid .conditional [M.empty, x v, base v] := by
  simp [evaluate, CheckedExpr.eval, DataOperations.ofModel, invalidExpr, Term.eval, Term.evalList,
    Data.Model.enum, h, x, xId, base, baseId]

example : B.holds (evaluate M numeral B v forcedExpr) := by
  simp [evaluate, CheckedExpr.eval, DataOperations.ofModel, forcedExpr, Term.eval, Logic.eval, B.holds_true]

/-- Image evaluation on an unrecognized bound follows the interpretation's policy. -/
private theorem image_on_invalid_bound
    (ops : DataOperations V) (isSet : V → Prop) (unspecified : V → V)
    (invalidImage : ∀ {set} (f : V → V), ¬ isSet set → ops.image set f = unspecified set)
    (invalidBound : ¬ isSet (base v)) :
    imageExpr.eval ops B (external ops) v = unspecified (base v) :=
  invalidImage id invalidBound

example (ops : DataOperations V) :
    numeralExpr.eval ops B (external ops) v = ops.numeral 12 := rfl

namespace EndpointExamples

private meta def resolveBody (body : String) (imports : ImportMap := [])
    (dependencies : Registry := []) : Except String CheckedRegistry := do
  let source ← (Surface.Parser.parseModule s!"---- MODULE ActionSlice ----\n{body}\n====").mapError reprStr
  (Resolution.resolveWith .levelSyntax (("action", .parsed source imports) :: dependencies)
    "action").mapError reprStr

private meta def endpointText := r#"CONSTANT C
VARIABLE x, y
Lift(e) == LET Local == {e, C} IN Local'
Current == {x, y}
Both == {Current, Lift({x, y})}
OuterWitness == \E w \in {x} : (w = y)'
InnerWitness == (\E w \in {x} : w = y)'
Future == []TRUE
Ignore(arg) == TRUE
IgnoredAction == Ignore(x')
THEOREM Future
"#

private meta def actionUnit (idx : Nat) : BindingId := .declared ⟨"action", [.unit idx]⟩
private meta def act (registry : CheckedRegistry) (idx : Nat) :=
  Endpoints.lowerAction registry [] fixtureSignature 40 (actionUnit idx)
private meta def atState (registry : CheckedRegistry) (idx : Nat) :=
  Endpoints.lowerState registry [] fixtureSignature 40 (actionUnit idx)

#guard match resolveBody endpointText with
  | .ok registry => match atState registry 4, act registry 3, act registry 7,
      atState registry 9, act registry 10, lowerDefinition registry fixtureSignature 40 (actionUnit 4) with
    | .error (.wrongLevel stateSite .state .action), .error (.wrongLevel actionSite .action .state),
      .error (.wrongLevel temporalSite .action .temporal), .ok ignored,
      .error (.lowering {kind := .expectedNullaryDefinition _, ..}),
      .error {kind := .primeRequiresLevels, site := primeSite} =>
      stateSite = ⟨"action", [.unit 4, .body]⟩ ∧ actionSite = ⟨"action", [.unit 3, .body]⟩ ∧
      temporalSite = ⟨"action", [.unit 7, .body]⟩ ∧ ignored.term.firstPrime.isNone ∧
      primeSite = ⟨"action", [.unit 2, .body, .body]⟩
    | _, _, _, _, _, _ => false
  | .error _ => false

#guard match resolveBody "VARIABLE v\nP(t) == t'\nBad == P(v')" with
  | .ok registry =>
    match act registry 2 with
    | .error (.levels diagnostic) =>
      diagnostic = ⟨⟨"action", [.unit 2, .body]⟩, .failedRequirement
        ⟨⟨"action", [.unit 1, .body, .operand 0]⟩, .atMost (.fixed .action) .state⟩⟩
    | _ => false
  | .error _ => false

#guard match resolveBody "VARIABLE v\nBad == (v')'" with
  | .ok registry =>
    match act registry 1 with
    | .error (.levels diagnostic) =>
      let inner : Site := ⟨"action", [.unit 1, .body, .operand 0]⟩
      diagnostic = ⟨inner, .failedRequirement ⟨inner, .atMost (.fixed .action) .state⟩⟩
    | _ => false
  | .error _ => false

#guard match resolveBody "VARIABLE v\nH(F(_)) == F(v)\nOut == v'" with
  | .ok registry =>
    match act registry 2 with
    | .error (.levels diagnostic) =>
      diagnostic = ⟨⟨"action", [.unit 1, .parameter 0]⟩, .unsupported .operatorParameter⟩
    | _ => false
  | .error _ => false

private meta def maskId : BindingId := .declared ⟨"std", [.member 0]⟩

-- A zero-weight argument can still occur in the expanded value passed to a primitive.
#guard match resolveBody "EXTENDS Std\nVARIABLE v\nHidden == Mask(v')\nNested == Hidden'"
    [("Std", "std")] [("std", .signature "Std" [] [.operator (.ident "Mask") [.expression]])] with
  | .ok registry =>
    let levels : Levels.ExternalLevels := [(maskId, ⟨.constant, [⟨.action, false⟩]⟩)]
    let admitted : ExternalSignature := fun id => if id = maskId then some 1 else none
    match Endpoints.lowerState registry levels admitted 40 (actionUnit 1),
      Endpoints.lowerAction registry levels admitted 40 (actionUnit 2) with
    | .error (.primeInState inner), .error (.lowering ⟨outer, .nestedPrime retained⟩) =>
      inner = ⟨"action", [.unit 1, .body, .argument 0]⟩ ∧ retained = inner ∧
      outer = ⟨"action", [.unit 2, .body]⟩
    | _, _ => false
  | .error _ => false

open Lean in
private meta def emitAction (idx : Nat) : Elab.Term.TermElabM Lean.Expr := do
  let result := (resolveBody endpointText).bind fun registry => (act registry idx).mapError reprStr
  let action ← match result with
    | .ok action => pure action
    | .error message => throwError "{message}"
  let term ← quoteTerm action.term
  let valid ← Meta.mkEqRefl (toExpr true)
  return mkApp3 (mkConst ``Endpoints.CheckedAction.mk) (mkConst ``fixtureSignature) term valid

private noncomputable def bothExpr : Endpoints.CheckedAction fixtureSignature := by_elab emitAction 4
private noncomputable def outerExpr : Endpoints.CheckedAction fixtureSignature := by_elab emitAction 5
private noncomputable def innerExpr : Endpoints.CheckedAction fixtureSignature := by_elab emitAction 6

variable (ends : Endpoints.EndpointValuation V)
private def xKey : BindingId := .declared ⟨"action", [.unit 1, .member 0]⟩
private def yKey : BindingId := .declared ⟨"action", [.unit 1, .member 1]⟩
private def cKey : BindingId := .declared ⟨"action", [.unit 0, .member 0]⟩

private noncomputable def observe (action : Endpoints.CheckedAction fixtureSignature) : V :=
  let ops := DataOperations.ofModel M numeral
  action.eval ops B (external ops) ends

private theorem compound_eq :
    observe M numeral B ends bothExpr =
      M.enum [M.enum [ends.source xKey, ends.source yKey],
        M.enum [M.enum [ends.target xKey, ends.target yKey], ends.rigid cKey]] := rfl

private theorem enclosing_witness_iff :
    B.holds (observe M numeral B ends outerExpr) ↔ ends.source xKey = ends.target yKey := by
  simp [observe, outerExpr, Endpoints.CheckedAction.eval, Term.eval, Term.evalList, withWitness,
    DataOperations.ofModel, Booleans.holds_ofProp, xKey, yKey]

private theorem primed_domain_iff :
    B.holds (observe M numeral B ends innerExpr) ↔ ends.target xKey = ends.target yKey := by
  simp [observe, innerExpr, Endpoints.CheckedAction.eval, Term.eval, Term.evalList, withWitness,
    DataOperations.ofModel, Booleans.holds_ofProp, xKey, yKey]

end EndpointExamples

end Silmaril.Logic.Temporal.TLA.DataElab.Examples
