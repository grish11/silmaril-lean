module

import Silmaril.Logic.Temporal.TLA.DataElab.Collections.Tagged
import all Silmaril.Logic.Temporal.TLA.DataElab.Collections.Defs
import all Silmaril.Logic.Temporal.TLA.DataElab.Defs
import Silmaril.Logic.Temporal.TLA.Data.Tagged.Collections.Binders.Thms
import Silmaril.Logic.Temporal.TLA.Data.Tagged.Collections.RecordSet.Thms
import Silmaril.Logic.Temporal.TLA.Data.Tagged.Except.Thms
import Silmaril.Logic.Temporal.TLA.Data.Thms
public import Silmaril.Logic.Temporal.TLA.Resolution.Names
public import Silmaril.Logic.Temporal.TLA.DataElab.Semantics
meta import Silmaril.Logic.Temporal.TLA.DataElab.Collections.Defs
meta import Silmaril.Logic.Temporal.TLA.Surface.Parser.Defs
public import Lean
public meta import Lean

/-! Checked parser-to-denotation regressions for the collection forms. -/

namespace Silmaril.Logic.Temporal.TLA.DataElab.Collections.Examples

open Resolution Data.Tagged

private meta def noPrimitives : ExternalSignature := fun _ => none

private meta def participantsId : BindingId := .declared ⟨"client", [.unit 0, .member 0]⟩

private meta def source := r#"---- MODULE CollectionChecks ----
CONSTANT p
Build == [k \in p |-> [key |-> k, ready |-> TRUE]]
RecordTypes == [key : {TRUE}, ready : BOOLEAN]
FunctionTypes == [p -> RecordTypes]
BadBound == [i \in TRUE |-> i]
BadRange == [p -> TRUE]
BadFields == [ok : BOOLEAN, bad : TRUE]
BadDomain == [TRUE -> BOOLEAN]
VARIABLES f, k, v
Lookup == Build[TRUE].ready
StringLookup == Build[TRUE]["ready"]
Domain == DOMAIN Build
TupleUpdate == [[i \in {<<TRUE, FALSE>>} |-> FALSE] EXCEPT ![TRUE, FALSE] = TRUE][TRUE, FALSE]
Read == f[k]
Repeat == [f EXCEPT !.cells[k] = IF @ THEN FALSE ELSE TRUE,
                     !.cells[k] = IF @ THEN FALSE ELSE TRUE]
Nested == [f EXCEPT ![k] = [@ EXCEPT ![@.pick] = IF @ THEN FALSE ELSE TRUE]]
BadAccess == TRUE[FALSE]
BadGraphDomain == DOMAIN FALSE
BadUpdate == [TRUE EXCEPT ![FALSE] = @]
Whole == <<(f[k])', (DOMAIN f)', ([f EXCEPT ![k] = @])'>>
Mixed == [f EXCEPT ![k'] = IF @ THEN v' ELSE v]
Flat == [i, j \in BOOLEAN, a \in {FALSE} |-> <<i, j, a>>]
NestedKey == [<<i, j>> \in {<<TRUE, FALSE>>}, a \in {FALSE} |-> <<i, j, a>>]
TupleKey == [<<i>> \in {<<FALSE>>, <<TRUE, FALSE>>, TRUE} |-> i]
GroupedImage == {<<i, j, a>> : i, j \in BOOLEAN, a \in {FALSE}}
TupleImage == {i : <<i>> \in {<<FALSE>>, <<TRUE, FALSE>>}}
ForAll == \A <<i, j>> \in {<<TRUE, FALSE>>, <<TRUE, TRUE, FALSE>>, FALSE}, a \in {FALSE} : j = a
Exists == \E <<i>> \in {<<FALSE, TRUE>>, FALSE} : TRUE
Filter == {<<i>> \in {<<TRUE>>, <<FALSE>>, <<TRUE, FALSE>>, TRUE} : i}
Choose == CHOOSE <<i, j>> \in {<<TRUE, FALSE>>, TRUE} : i
ChooseNone == CHOOSE <<i>> \in {<<TRUE, FALSE>>, TRUE} : TRUE
ChooseUnbounded == CHOOSE <<i>> : i = TRUE
BadProduct == [i, j \in BOOLEAN, a \in FALSE |-> i]
EmptyProduct == [i, j \in BOOLEAN, a \in {} |-> <<i, j, a>>]
PrimeBound == \E <<i>> \in k', a \in {FALSE} : i = a
====
"#

private meta def registryFor (text : String) : Except String CheckedRegistry := do
  let parsed ← (Surface.Parser.parseModule text).mapError reprStr
  (Resolution.resolve [("client", .parsed parsed [])] "client").mapError reprStr

private meta def select (registry : CheckedRegistry) (name : String) : Except String BindingId := do
  let some binding := (registry.moduleAt registry.root).bind (·.bindingAt (.ident name))
    | throw s!"missing definition {name}"
  return binding.id

private meta def lower (name : String) (action : Bool := false) :
    Except String (CheckedExpr noPrimitives .collections) := do
  let registry ← registryFor source
  let id ← select registry name
  if action then
    (Collections.lowerAction registry [] noPrimitives 40 id).map (·.expression) |>.mapError reprStr
  else (Collections.lowerState registry [] noPrimitives 40 id).mapError reprStr

private meta def rejects (definition : String) (path : Path) (kind : DiagnosticKind) : Bool :=
  let result := do
    let registry ← registryFor s!"---- MODULE Rejected ----\nOut == {definition}\n===="
    let id ← select registry "Out"
    return Collections.lowerState registry [] noPrimitives 40 id
  match result with
  | .ok (.error (.lowering diagnostic)) => diagnostic = ⟨⟨"client", .unit 0 :: .body :: path⟩, kind⟩
  | _ => false

#guard rejects "[a |-> TRUE, a |-> FALSE]" [.field 1] (.duplicateField "a")
#guard rejects "[a : BOOLEAN, a : {TRUE}]" [.field 1] (.duplicateField "a")
#guard rejects "[a |-> TRUE][1.0]" [.operand 1] (.unsupported .literal)
#guard rejects "[[a |-> TRUE] EXCEPT ![TRUE, 1.0] = @]"
  [.update 0, .updateComponent 0, .argument 1] (.unsupported .literal)

private meta def rejectsName (expression : String) (path : Path) (kind : Resolution.DiagnosticKind) : Bool :=
  match Surface.Parser.parseModule s!"---- MODULE Rejected ----\nOut == {expression}\n====" with
  | .ok parsed =>
    match Resolution.resolve [("client", .parsed parsed [])] "client" with
    | .error diagnostic => diagnostic = ⟨⟨"client", [.unit 0, .body] ++ path⟩, kind⟩
    | _ => false
  | _ => false

#guard rejectsName "[i \\in BOOLEAN, j \\in {i} |-> j]" [.bound 1, .domain, .operand 0]
  (.unknownName (.ident "i"))
#guard rejectsName "{i : <<i, j>> \\in BOOLEAN, i \\in BOOLEAN}" [.bound 1, .binder 0]
  (.conflictingName (.ident "i") (.declared ⟨"client", [.unit 0, .body, .bound 0, .binder 0]⟩))

#guard match registryFor source with
  | .ok registry =>
    match select registry "PrimeBound" with
    | .ok (.declared site) =>
      match Collections.lowerState registry [] noPrimitives 40 (.declared site), lower "PrimeBound" true with
      | .error (.wrongLevel body .state .action), .ok checked =>
        body = site.child .body ∧ checked.term.firstPrime = some (body.child (.bound 0) |>.child .domain)
      | _, _ => false
    | _ => false
  | _ => false

#guard !(Term.bounded (signature := noPrimitives) rfl (.map .function)
  [([.name 0], .booleanSet), ([.name 1], .witness 0)] (.witness 1)).isWellFormed []

#guard match Surface.Parser.parseExpr "[f EXCEPT ![] = @]" with
  | .error diagnostic => diagnostic.kind == .syntax
  | _ => false

#guard match Surface.Parser.parseModule "---- MODULE Rejected ----\nOut == [TRUE EXCEPT ![@] = FALSE]\n====" with
  | .ok parsed =>
    match Resolution.resolve [("client", .parsed parsed [])] "client" with
    | .error diagnostic =>
      diagnostic = ⟨⟨"client", [.unit 0, .body, .update 0, .updateComponent 0, .argument 0]⟩,
        .oldValueOutOfScope⟩
    | _ => false
  | _ => false

#guard
  let result := do
    let registry ← registryFor r#"---- MODULE Rejected ----
VARIABLE f
Shift(a) == a'
Out == [f EXCEPT ![TRUE] = Shift(@)]
====
"#
    let id ← select registry "Out"
    return Collections.lowerAction registry [] noPrimitives 40 id
  match result with
  | .ok (.error (.lowering diagnostic)) =>
    diagnostic = ⟨⟨"client", [.unit 1, .body]⟩, .primeCrossesOldValue⟩
  | _ => false

#guard match registryFor source with
  | .ok registry =>
    match Endpoints.lowerState registry [] noPrimitives 40 (.declared ⟨"client", [.unit 1]⟩) with
    | .error (.lowering diagnostic) =>
      diagnostic = ⟨⟨"client", [.unit 1, .body]⟩, .unsupported .function⟩
    | _ => false
  | _ => false

#guard match lower "Build" with
  | .ok checked =>
    match checked.term with
    | .function _ site binder slot (.rigid domain) (.record _ bodySite [("key", .witness use), _]) =>
      site = ⟨"client", [.unit 1, .body]⟩ ∧
        binder = .declared (site.child (.bound 0) |>.child (.binder 0)) ∧
        bodySite = site.child .body ∧ domain = participantsId ∧ slot = use
    | _ => false
  | _ => false

meta section

open Lean

deriving instance ToExpr for Resolution.Fixity
deriving instance ToExpr for Resolution.Name
deriving instance ToExpr for Step
deriving instance ToExpr for Site
deriving instance ToExpr for BindingId
deriving instance ToExpr for Surface.Quantifier
deriving instance ToExpr for BinderMap
deriving instance ToExpr for BinderPattern
deriving instance ToExpr for Bounded

-- Stage the actual expansion. The kernel checks the quoted syntax and its scope.
private partial def quoteTerm (term : Term noPrimitives .collections) :
    Elab.Term.TermElabM Lean.Expr := do
  let initial := fun ctor => mkApp2 (mkConst ctor) (mkConst ``noPrimitives)
    (mkConst ``Fragment.collections)
  let type := initial ``Term
  let node := fun name args => mkAppN (initial name) args
  let enabled ← Meta.mkEqRefl (mkConst ``Fragment.collections)
  let terms := fun values => do Meta.mkListLit type (← values.mapM quoteTerm)
  let fields := fun (values : List (String × Term noPrimitives .collections)) => do
    let pair := mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``String) type
    Meta.mkListLit pair (← values.mapM fun (name, value) => do
      return mkApp4 (mkConst ``Prod.mk [0, 0]) (mkConst ``String) type (toExpr name) (← quoteTerm value))
  match term with
  | .rigid id => return node ``Term.rigid #[toExpr id]
  | .flexible id => return node ``Term.flexible #[toExpr id]
  | .witness slot => return node ``Term.witness #[toExpr slot]
  | .numeral n => return node ``Term.numeral #[toExpr n]
  | .boolean b => return node ``Term.boolean #[toExpr b]
  | .booleanSet => return node ``Term.booleanSet #[]
  | .ite c y n => return node ``Term.ite #[← quoteTerm c, ← quoteTerm y, ← quoteTerm n]
  | .eq negated lhs rhs => return node ``Term.eq #[toExpr negated, ← quoteTerm lhs, ← quoteTerm rhs]
  | .prime site arg => return node ``Term.prime #[toExpr site, ← quoteTerm arg]
  | .enum values => return node ``Term.enum #[← terms values]
  | .function _ site binder slot domain body =>
    return node ``Term.function #[enabled, toExpr site, toExpr binder, toExpr slot,
      ← quoteTerm domain, ← quoteTerm body]
  | .chooseTuple _ slots bound body =>
    let domain ← match bound with
      | none => Meta.mkAppOptM ``Option.none #[some type]
      | some domain => Meta.mkAppM ``Option.some #[← quoteTerm domain]
    return node ``Term.chooseTuple #[enabled, toExpr slots, domain, ← quoteTerm body]
  | .bounded _ kind groups body =>
    let groupType ← Meta.mkAppM ``Prod #[toTypeExpr (List BinderPattern), type]
    let domains ← groups.mapM fun (patterns, domain) => do
      Meta.mkAppM ``Prod.mk #[toExpr patterns, ← quoteTerm domain]
    return node ``Term.bounded #[enabled, toExpr kind, ← Meta.mkListLit groupType domains, ← quoteTerm body]
  | .functionSet _ site domain range =>
    return node ``Term.functionSet #[enabled, toExpr site, ← quoteTerm domain, ← quoteTerm range]
  | .record _ site values => return node ``Term.record #[enabled, toExpr site, ← fields values]
  | .recordSet _ site values => return node ``Term.recordSet #[enabled, toExpr site, ← fields values]
  | .graphDomain _ arg => return node ``Term.graphDomain #[enabled, ← quoteTerm arg]
  | .index _ fn key => return node ``Term.index #[enabled, ← quoteTerm fn, ← quoteTerm key]
  | .tuple _ values => return node ``Term.tuple #[enabled, ← terms values]
  | .string _ value => return node ``Term.string #[enabled, toExpr value]
  | .oldValue _ slot => return node ``Term.oldValue #[enabled, toExpr slot]
  | .except _ root clauses =>
    let clauses ← clauses.mapM fun (slot, keys, body) => do
      let rhs ← Meta.mkAppM ``Prod.mk #[← terms keys, ← quoteTerm body]
      Meta.mkAppM ``Prod.mk #[toExpr slot, rhs]
    let rhsType ← Meta.mkAppM ``Prod #[mkApp (mkConst ``List [0]) type, type]
    let clauseType ← Meta.mkAppM ``Prod #[mkConst ``Nat, rhsType]
    return node ``Term.except #[enabled, ← quoteTerm root, ← Meta.mkListLit clauseType clauses]
  | other => throwError "unexpected expanded term: {reprStr other}"

private def emit (name : String) (action : Bool := false) : Elab.Term.TermElabM Lean.Expr := do
  match lower name action with
  | .error message => throwError "{message}"
  | .ok checked =>
    let expression := mkApp4 (mkConst ``CheckedExpr.mk) (mkConst ``noPrimitives) (mkConst ``Fragment.collections)
      (← quoteTerm checked.term) (← Meta.mkEqRefl (toExpr true))
    if action then return mkApp2 (mkConst ``Collections.CheckedAction.mk) (mkConst ``noPrimitives) expression
    else return expression

end

private noncomputable def build : CheckedExpr noPrimitives .collections := by_elab emit "Build"
private noncomputable def recordTypes : CheckedExpr noPrimitives .collections := by_elab emit "RecordTypes"
private noncomputable def functionTypes : CheckedExpr noPrimitives .collections := by_elab emit "FunctionTypes"
private noncomputable def badBound : CheckedExpr noPrimitives .collections := by_elab emit "BadBound"
private noncomputable def badRange : CheckedExpr noPrimitives .collections := by_elab emit "BadRange"
private noncomputable def badFields : CheckedExpr noPrimitives .collections := by_elab emit "BadFields"
private noncomputable def badDomain : CheckedExpr noPrimitives .collections := by_elab emit "BadDomain"
private noncomputable def lookup : CheckedExpr noPrimitives .collections := by_elab emit "Lookup"
private noncomputable def stringLookup : CheckedExpr noPrimitives .collections := by_elab emit "StringLookup"
private noncomputable def domainExpr : CheckedExpr noPrimitives .collections := by_elab emit "Domain"
private noncomputable def tupleUpdate : CheckedExpr noPrimitives .collections := by_elab emit "TupleUpdate"
private noncomputable def read : CheckedExpr noPrimitives .collections := by_elab emit "Read"
private noncomputable def repeated : CheckedExpr noPrimitives .collections := by_elab emit "Repeat"
private noncomputable def nested : CheckedExpr noPrimitives .collections := by_elab emit "Nested"
private noncomputable def badAccess : CheckedExpr noPrimitives .collections := by_elab emit "BadAccess"
private noncomputable def badGraphDomain : CheckedExpr noPrimitives .collections := by_elab emit "BadGraphDomain"
private noncomputable def badUpdate : CheckedExpr noPrimitives .collections := by_elab emit "BadUpdate"
private noncomputable def whole : Collections.CheckedAction noPrimitives := by_elab emit "Whole" true
private noncomputable def mixed : Collections.CheckedAction noPrimitives := by_elab emit "Mixed" true
private noncomputable def flat : CheckedExpr noPrimitives .collections := by_elab emit "Flat"
private noncomputable def nestedKey : CheckedExpr noPrimitives .collections := by_elab emit "NestedKey"
private noncomputable def tupleKey : CheckedExpr noPrimitives .collections := by_elab emit "TupleKey"
private noncomputable def groupedImage : CheckedExpr noPrimitives .collections := by_elab emit "GroupedImage"
private noncomputable def tupleImage : CheckedExpr noPrimitives .collections := by_elab emit "TupleImage"
private noncomputable def forallExpr : CheckedExpr noPrimitives .collections := by_elab emit "ForAll"
private noncomputable def existsExpr : CheckedExpr noPrimitives .collections := by_elab emit "Exists"
private noncomputable def filterExpr : CheckedExpr noPrimitives .collections := by_elab emit "Filter"
private noncomputable def chooseExpr : CheckedExpr noPrimitives .collections := by_elab emit "Choose"
private noncomputable def chooseNone : CheckedExpr noPrimitives .collections := by_elab emit "ChooseNone"
private noncomputable def chooseUnbounded : CheckedExpr noPrimitives .collections := by_elab emit "ChooseUnbounded"
private noncomputable def badProduct : CheckedExpr noPrimitives .collections := by_elab emit "BadProduct"
private noncomputable def emptyProduct : CheckedExpr noPrimitives .collections := by_elab emit "EmptyProduct"

universe u
variable (policy : Tagged.Policy.{u}) (invalid : Tagged.CollectionPolicy.{u})

private def noExternal : ExternalInterpretation Value.{u} noPrimitives :=
  fun _ _ impossible => nomatch impossible

private noncomputable def valuation (domain : SetData.{u}) : Valuation Value.{u} :=
  ⟨fun id => if id = participantsId then .set domain else .boolean false, fun _ => .boolean false⟩

private noncomputable def evaluate (expr : CheckedExpr noPrimitives .collections)
    (domain : SetData.{u}) : Value.{u} :=
  expr.eval (policy.collectionOperations invalid) policy.booleans noExternal (valuation domain)

private noncomputable def recordBody (invalid : Tagged.CollectionPolicy.{u}) (key : Value.{u})
    (field : String) : Value.{u} :=
  let fields := [("key", key), ("ready", Value.boolean true)]
  (fields.lookup field).getD (invalid (.record fields))

private theorem build_eq (domain : SetData.{u}) :
    evaluate policy invalid build domain =
      .function (Graph.ofFn domain fun x => .record ["key", "ready"] (recordBody invalid x)) := by
  simp [evaluate, CheckedExpr.eval, build, Term.eval, Term.evalFields, Operations.collection,
    Tagged.Policy.collectionOperations, valuation, participantsId, withWitness, Tagged.Policy.booleans]
  rfl

private theorem built_graph (domain : SetData.{u}) :
    ∃ g : Graph.{u}, evaluate policy invalid build domain = .function g ∧
      g.domain = domain ∧ ∀ key, domain.mem key →
        ∃ r : Graph.{u}, g.lookup key = some (.function r) ∧
          r.domain = SetData.enum [Value.string "key", Value.string "ready"] ∧
          r.lookup (.string "key") = some key ∧ r.lookup (.string "ready") = some (.boolean true) := by
  rw [build_eq]
  refine ⟨_, rfl, Graph.domain_ofFn _ _, ?_⟩
  intro key hk
  refine ⟨_, Graph.lookup_ofFn hk, Graph.domain_record _ _, ?_, ?_⟩
  · exact Graph.lookup_record (recordBody invalid key) (name := "key") (by simp)
  · exact Graph.lookup_record (recordBody invalid key) (name := "ready") (by simp)

private def trueSet : SetData.{u} := SetData.enum [Value.boolean true]
private def boolSet : SetData.{u} := SetData.enum [Value.boolean true, Value.boolean false]

private def fieldSets : List (String × SetData.{u}) := [("key", trueSet), ("ready", boolSet)]

private theorem recordTypes_eq (domain : SetData.{u}) :
    evaluate policy invalid recordTypes domain = .set (SetData.recordSet fieldSets) := by
  simp [evaluate, CheckedExpr.eval, recordTypes, Term.eval, Term.evalFields, Term.evalList,
    Operations.collection, Tagged.Policy.collectionOperations, Tagged.Policy.operations,
    Tagged.Policy.booleans, fieldSets, trueSet, boolSet, Value.recordSet, Value.checkRecordSetFields,
    Value.decodeRecordSetBounds, Except.map]

private theorem functionTypes_eq (domain : SetData.{u}) :
    evaluate policy invalid functionTypes domain =
      .set (domain.functionSet (SetData.recordSet fieldSets)) := by
  simp [evaluate, CheckedExpr.eval, functionTypes, Term.eval, Term.evalFields, Term.evalList,
    Operations.collection, Tagged.Policy.collectionOperations, Tagged.Policy.operations,
    Tagged.Policy.booleans, valuation, participantsId, fieldSets, trueSet, boolSet, Value.recordSet,
    Value.checkRecordSetFields, Value.decodeRecordSetBounds, Except.map]

private theorem recognizes_record (domain : SetData.{u}) (g : Graph.{u}) :
    (Value.function g).mem (evaluate policy invalid recordTypes domain) ↔
      g.domain = SetData.enum [Value.string "key", Value.string "ready"] ∧
      g.lookup (.string "key") = some (.boolean true) ∧
      ∃ b : Bool, g.lookup (.string "ready") = some (.boolean b) := by
  rw [recordTypes_eq, Value.mem_set, SetData.mem_recordSet]
  simp only [Value.function_injective.eq_iff, exists_eq_left]
  constructor
  · rintro ⟨hd, fits⟩
    obtain ⟨key, hkey, htrue⟩ := fits "key" trueSet (by simp [fieldSets])
    obtain ⟨ready, hready, hbool⟩ := fits "ready" boolSet (by simp [fieldSets])
    simp [trueSet, SetData.mem_enum] at htrue
    refine ⟨hd, htrue ▸ hkey, ?_⟩
    simp [boolSet, SetData.mem_enum] at hbool
    rcases hbool with h | h
    · exact ⟨true, h ▸ hready⟩
    · exact ⟨false, h ▸ hready⟩
  · rintro ⟨hd, hkey, b, hready⟩
    refine ⟨hd, ?_⟩
    intro name bound h
    simp only [fieldSets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h
    · cases h
      exact ⟨_, hkey, by simp [trueSet, SetData.mem_enum]⟩
    · cases h
      exact ⟨_, hready, by cases b <;> simp [boolSet, SetData.mem_enum]⟩

private theorem recognizes_function (domain : SetData.{u}) (candidate : Value.{u}) :
    candidate.mem (evaluate policy invalid functionTypes domain) ↔
      ∃ g : Graph.{u}, .function g = candidate ∧ g.domain = domain ∧
        ∀ key value, g.relates key value → value.mem (evaluate policy invalid recordTypes domain) := by
  rw [functionTypes_eq, recordTypes_eq, Value.mem_set, SetData.mem_functionSet]
  simp only [Value.mem_set]

private theorem invalid_bound (domain : SetData.{u}) :
    evaluate policy invalid badBound domain = invalid (.function (.boolean true)) := by
  simp [evaluate, CheckedExpr.eval, badBound, Term.eval, Operations.collection,
    Tagged.Policy.collectionOperations, Tagged.Policy.booleans]

private theorem invalid_range (domain : SetData.{u}) :
    evaluate policy invalid badRange domain = invalid (.functionSet (.set domain) (.boolean true)) := by
  simp [evaluate, CheckedExpr.eval, badRange, Term.eval, Operations.collection,
    Tagged.Policy.collectionOperations, Tagged.Policy.booleans, valuation, participantsId]

private theorem invalid_domain (domain : SetData.{u}) :
    evaluate policy invalid badDomain domain = invalid (.functionSet (.boolean true) (.set boolSet)) := by
  simp [evaluate, CheckedExpr.eval, badDomain, Term.eval, Operations.collection,
    Tagged.Policy.collectionOperations, Tagged.Policy.operations, Tagged.Policy.booleans, boolSet]

private theorem invalid_fields (domain : SetData.{u}) :
    evaluate policy invalid badFields domain =
      invalid (.recordSet (.nonSetBound "bad") [("ok", .set boolSet), ("bad", .boolean true)]) := by
  simp [evaluate, CheckedExpr.eval, badFields, Term.eval, Term.evalFields, Operations.collection,
    Tagged.Policy.collectionOperations, Tagged.Policy.operations, Tagged.Policy.booleans, boolSet,
    Value.recordSet, Value.checkRecordSetFields, Value.decodeRecordSetBounds, Except.map]

private theorem domain_eq (domain : SetData.{u}) :
    evaluate policy invalid domainExpr domain = .set domain := by
  change Value.domain policy.numeric (evaluate policy invalid build domain) = _
  simp [build_eq]

private theorem lookup_eq (domain : SetData.{u}) (h : domain.mem (Value.boolean true)) :
    evaluate policy invalid lookup domain = .boolean true := by
  change Value.apply policy.numeric
    (Value.apply policy.numeric (evaluate policy invalid build domain) (.boolean true))
    (.string "ready") = _
  obtain ⟨_, hbuild, _, hlookup⟩ := built_graph policy invalid domain
  obtain ⟨_, hr, _, _, hready⟩ := hlookup _ h
  rw [hbuild, Value.apply_function _ (Graph.lookup_eq_some.mp hr)]
  exact Value.apply_function _ (Graph.lookup_eq_some.mp hready)

private theorem string_lookup_eq (domain : SetData.{u}) :
    evaluate policy invalid stringLookup domain = evaluate policy invalid lookup domain := rfl

private theorem tuple_update_eq (domain : SetData.{u}) :
    evaluate policy invalid tupleUpdate domain = .boolean true := by
  let key := Value.tuple.{u} [.boolean true, .boolean false]
  let bound := SetData.enum [key]
  change Value.apply policy.numeric (Value.updatePath policy.numeric
    ((policy.collectionOperations invalid).function (.set bound) (fun _ => .boolean false))
    [key] (fun _ => .boolean true)) key = _
  rw [show (policy.collectionOperations invalid).function (.set bound) (fun _ => .boolean false) =
      .function (Graph.ofFn bound (fun _ => .boolean false)) by
    simp [Tagged.Policy.collectionOperations], Value.updatePath_single, Value.update_function]
  apply Value.apply_function
  apply Graph.lookup_eq_some.mp
  apply Graph.lookup_update
  simp [bound, SetData.mem_enum]

private def fId : BindingId := .declared ⟨"client", [.unit 8, .member 0]⟩
private def kId : BindingId := .declared ⟨"client", [.unit 8, .member 1]⟩
private def vId : BindingId := .declared ⟨"client", [.unit 8, .member 2]⟩

private noncomputable def atState (expr : CheckedExpr noPrimitives .collections)
    (state : Valuation Value.{u}) : Value.{u} :=
  expr.eval (policy.collectionOperations invalid) policy.booleans noExternal state

private noncomputable def atEndpoints (action : Collections.CheckedAction noPrimitives)
    (endpoints : Endpoints.EndpointValuation Value.{u}) : Value.{u} :=
  action.eval (policy.collectionOperations invalid) policy.booleans noExternal endpoints

open Classical in
private noncomputable def conditional (B : Booleans Value.{u}) (guard yes no : Value.{u}) : Value.{u} :=
  if B.IsBoolean guard then
    if B.holds guard then yes else no
  else B.invalid .conditional [guard, yes, no]

private noncomputable def flip (old : Value.{u}) : Value.{u} :=
  conditional policy.booleans old (.boolean false) (.boolean true)

private theorem repeated_eq (state : Valuation Value.{u}) :
    atState policy invalid repeated state =
      let path := [Value.string "cells", state.flexible kId]
      let clause : ExceptClause := ⟨path, flip policy⟩
      Value.updateClauses policy.numeric (state.flexible fId) [clause, clause] := rfl

private theorem repeated_leaf (state : Valuation Value.{u})
    (h : (state.flexible fId).lookupPath [.string "cells", state.flexible kId] = .found (.boolean true)) :
    (atState policy invalid repeated state).lookupPath [.string "cells", state.flexible kId] =
      .found (.boolean true) := by
  rw [repeated_eq, Value.updateClauses_cons, Value.updateClauses_cons, Value.updateClauses_nil]
  have once := Value.lookupPath_update_found policy.numeric (replacement := flip policy) h
  have twice := Value.lookupPath_update_found policy.numeric (replacement := flip policy) once
  simpa [flip, conditional, Tagged.Policy.booleans, Booleans.IsBoolean, Value.boolean_injective.eq_iff]
    using twice

private theorem repeated_missing (state : Valuation Value.{u})
    (h : (state.flexible fId).lookupPath [.string "cells", state.flexible kId] = .missingKey) :
    atState policy invalid repeated state = state.flexible fId := by
  rw [repeated_eq, Value.updateClauses_cons, Value.updatePath_missing _ h,
    Value.updateClauses_cons, Value.updatePath_missing _ h, Value.updateClauses_nil]

private theorem nested_eq (state : Valuation Value.{u}) :
    atState policy invalid nested state =
      Value.updatePath policy.numeric (state.flexible fId) [state.flexible kId] (fun outer =>
        outer.updatePath policy.numeric [outer.apply policy.numeric (.string "pick")] (flip policy)) := rfl

private theorem missing_access (state : Valuation Value.{u}) (g : Graph.{u})
    (hf : state.flexible fId = .function g) (hk : ¬ g.domain.mem (state.flexible kId)) :
    atState policy invalid read state = policy.numeric .apply [.function g, state.flexible kId] := by
  change Value.apply policy.numeric (state.flexible fId) (state.flexible kId) = _
  rw [hf, Value.apply_missing _ hk]

private theorem invalid_access (state : Valuation Value.{u}) :
    atState policy invalid badAccess state = policy.numeric .apply [.boolean true, .boolean false] :=
  Value.apply_nonfunction _ (Value.asFunction_boolean true)

private theorem invalid_graph_domain (state : Valuation Value.{u}) :
    atState policy invalid badGraphDomain state = policy.numeric .domain [.boolean false] :=
  Value.domain_nonfunction _ (Value.asFunction_boolean false)

private theorem invalid_update (state : Valuation Value.{u}) :
    atState policy invalid badUpdate state = policy.numeric .update
      [.boolean true, .boolean false, policy.numeric .apply [.boolean true, .boolean false]] := by
  change Value.updatePath policy.numeric (Value.boolean true) [.boolean false] id = _
  rw [Value.updatePath_nonfunction _ (Value.asFunction_boolean true), Value.updatePath_nil, id]

private theorem whole_operand_eq (e : Endpoints.EndpointValuation Value.{u}) :
    atEndpoints policy invalid whole e = Value.tuple
      [(e.target fId).apply policy.numeric (e.target kId), (e.target fId).domain policy.numeric,
        (e.target fId).updatePath policy.numeric [e.target kId] id] := rfl

private theorem mixed_endpoint_eq (e : Endpoints.EndpointValuation Value.{u}) (g : Graph.{u})
    (hf : e.source fId = .function g) (h : g.relates (e.target kId) (.boolean true)) :
    atEndpoints policy invalid mixed e = .function (g.update (e.target kId) (e.target vId)) := by
  change Value.updatePath policy.numeric (e.source fId) [e.target kId]
    (fun old => conditional policy.booleans old (e.target vId) (e.source vId)) = _
  rw [hf, Value.updatePath_single, Value.apply_function _ h, Value.update_function]
  simp [conditional, Tagged.Policy.booleans, Booleans.IsBoolean]

private abbrev t : Value.{u} := .boolean true
private abbrev f : Value.{u} := .boolean false

private theorem cartesian_values (a b c : SetData.{u}) :
    Value.cartesian [.set a, .set b, .set c] = some (.set (SetData.cartesian [a, b, c])) :=
  Value.cartesian_sets [a, b, c]

private theorem untuple_wrong_length {arity : Nat} {xs : List Value.{u}} (h : xs.length ≠ arity) :
    (Value.tuple xs).untuple arity = none := by
  rw [Value.untuple_eq_none]
  rintro ⟨ys, hlen, heq⟩
  exact h ((Graph.tuple_injective (Value.function_injective heq)) ▸ hlen)

private theorem untuple_boolean (arity : Nat) (b : Bool) : (Value.boolean.{u} b).untuple arity = none :=
  Value.untuple_eq_none.mpr fun ⟨_, _, h⟩ => Value.function_ne_boolean _ _ h

private theorem flat_function (state : Valuation Value.{u}) :
    ∃ g : Graph.{u}, atState policy invalid flat state = .function g ∧
      g.domain = SetData.cartesian [boolSet, boolSet, SetData.enum [f]] ∧
      g.lookup (Value.tuple [t, f, f]) = some (Value.tuple [t, f, f]) := by
  have key : (SetData.cartesian [boolSet, boolSet, SetData.enum [f]]).mem (Value.tuple [t, f, f]) :=
    SetData.mem_cartesian.mpr ⟨[t, f, f], by repeat first | apply List.Forall₂.cons | apply List.Forall₂.nil | simp [boolSet], rfl⟩
  simp only [atState, CheckedExpr.eval, flat, Term.eval, Term.evalBounds, Term.evalList,
    Operations.collection, BinderMap.eval, Bounded.axes, Tagged.Policy.collectionOperations,
    Tagged.Policy.operations, Tagged.Policy.booleans, List.flatMap_cons, List.flatMap_nil,
    List.map_cons, List.map_nil, List.nil_append, List.cons_append, List.length_cons, List.length_nil, Nat.reduceAdd,
    cast_eq, Bool.false_eq_true, ite_false, show SetData.enum [t, f] = boolSet from rfl,
    cartesian_values, Value.asSet_set]
  refine ⟨_, rfl, Graph.domain_ofFn _ _, ?_⟩
  rw [Graph.lookup_ofFn key, show (Value.tuple [t, f, f]).untuple 3 = some [t, f, f] from Value.untuple_tuple [t, f, f]]
  rfl

private theorem grouped_image (state : Valuation Value.{u}) :
    (Value.tuple [f, t, f]).mem (atState policy invalid groupedImage state) := by
  have key : (SetData.cartesian [boolSet, boolSet, SetData.enum [f]]).mem (Value.tuple [f, t, f]) :=
    SetData.mem_cartesian.mpr ⟨[f, t, f], by repeat first | apply List.Forall₂.cons | apply List.Forall₂.nil | simp [boolSet], rfl⟩
  simp only [atState, CheckedExpr.eval, groupedImage, Term.eval, Term.evalBounds, Term.evalList,
    Operations.collection, BinderMap.eval, Bounded.axes, Tagged.Policy.collectionOperations,
    Tagged.Policy.operations, Tagged.Policy.booleans, List.flatMap_cons, List.flatMap_nil,
    List.map_cons, List.map_nil, List.nil_append, List.cons_append, List.length_cons, List.length_nil, Nat.reduceAdd,
    cast_eq, Bool.false_eq_true, ite_false, show SetData.enum [t, f] = boolSet from rfl,
    cartesian_values, Value.asSet_set, Value.mem_set]
  rw [SetData.mem_image]
  refine ⟨_, key, ?_⟩
  rw [show (Value.tuple [f, t, f]).untuple 3 = some [f, t, f] from Value.untuple_tuple [f, t, f]]
  rfl

private theorem nested_key (state : Valuation Value.{u}) :
    ∃ g : Graph.{u}, atState policy invalid nestedKey state = .function g ∧
      g.domain = SetData.cartesian [SetData.enum [Value.tuple [t, f]], SetData.enum [f]] ∧
      g.lookup (Value.tuple [Value.tuple [t, f], f]) = some (Value.tuple [t, f, f]) := by
  let pair := Value.tuple [t, f]
  let left := SetData.enum [pair]
  let right := SetData.enum [f]
  have product : Value.cartesian [.set left, .set right] = some (.set (SetData.cartesian [left, right])) :=
    Value.cartesian_sets [left, right]
  have key : (SetData.cartesian [left, right]).mem (Value.tuple [pair, f]) :=
    SetData.mem_cartesian.mpr ⟨[pair, f], .cons (by simp [left]) (.cons (by simp [right]) .nil), rfl⟩
  simp only [atState, CheckedExpr.eval, nestedKey, Term.eval, Term.evalBounds, Term.evalList,
    Operations.collection, BinderMap.eval, Bounded.axes, Tagged.Policy.collectionOperations,
    Tagged.Policy.operations, Tagged.Policy.booleans, List.flatMap_cons, List.flatMap_nil,
    List.map_cons, List.map_nil, List.nil_append, List.cons_append, List.length_cons, List.length_nil, Nat.reduceAdd,
    cast_eq, Bool.false_eq_true, ite_true, ite_false, show Value.tuple [t, f] = pair from rfl,
    show SetData.enum [pair] = left from rfl, show SetData.enum [f] = right from rfl]
  rw [product]
  simp only [Value.asSet_set]
  refine ⟨_, rfl, Graph.domain_ofFn _ _, ?_⟩
  rw [Graph.lookup_ofFn key,
    show (Value.tuple [pair, f]).untuple 2 = some [pair, f] from Value.untuple_tuple [pair, f]]
  change some (Value.tuple [_, _, f]) = _
  simp only [List.zip_cons_cons, List.zip_nil_left, List.foldl_cons, List.foldl_nil,
    BinderPattern.bindTotal, List.length_cons, List.length_nil, Nat.reduceAdd, show pair.untuple 2 = some [t, f] from Value.untuple_tuple [t, f], Option.getD_some]
  rfl

private theorem tuple_key_keeps_domain (state : Valuation Value.{u}) :
    ∃ g : Graph.{u}, atState policy invalid tupleKey state = .function g ∧
      g.domain = SetData.enum [Value.tuple [f], Value.tuple [t, f], t] ∧
      g.lookup (Value.tuple [f]) = some f ∧
      g.lookup (Value.tuple [t, f]) = some (Value.apply policy.numeric policy.choice.noWitness (.integer 1)) := by
  simp only [atState, CheckedExpr.eval, tupleKey, Term.eval, Term.evalBounds, Term.evalList,
    Operations.collection, BinderMap.eval, Bounded.axes, Tagged.Policy.collectionOperations,
    Tagged.Policy.operations, Tagged.Policy.booleans, cast_eq, List.flatMap_cons, List.flatMap_nil,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    Bool.false_eq_true, ite_true, ite_false, Value.asSet_set]
  refine ⟨_, rfl, Graph.domain_ofFn _ _, ?_, ?_⟩
  · rw [Graph.lookup_ofFn (by simp)]
    simp only [BinderPattern.bindTotal, List.length_cons, List.length_nil, Nat.reduceAdd,
      show (Value.tuple [f]).untuple 1 = some [f] from Value.untuple_tuple [f], Option.getD_some]
    rfl
  · rw [Graph.lookup_ofFn (by simp)]
    simp only [BinderPattern.bindTotal, List.length_cons, List.length_nil, Nat.reduceAdd,
      untuple_wrong_length.{u} (xs := [t, f]) (arity := 1) (by decide), Option.getD_none]
    rfl

private theorem tuple_image_keeps_member (state : Valuation Value.{u}) :
    (Value.apply policy.numeric policy.choice.noWitness (.integer 1)).mem
      (atState policy invalid tupleImage state) := by
  simp only [atState, CheckedExpr.eval, tupleImage, Term.eval, Term.evalBounds, Term.evalList,
    Operations.collection, BinderMap.eval, Bounded.axes, Tagged.Policy.collectionOperations,
    Tagged.Policy.operations, Tagged.Policy.booleans, cast_eq, List.flatMap_cons, List.flatMap_nil,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    Bool.false_eq_true, ite_true, ite_false, Value.asSet_set, Value.mem_set, SetData.mem_image]
  refine ⟨Value.tuple [t, f], by simp, ?_⟩
  simp only [BinderPattern.bindTotal, List.length_cons, List.length_nil, Nat.reduceAdd,
    untuple_wrong_length.{u} (xs := [t, f]) (arity := 1) (by decide), Option.getD_none]
  rfl

private theorem tuple_forall (state : Valuation Value.{u}) :
    atState policy invalid forallExpr state = t := by
  change policy.booleans.holds (policy.booleans.ofProp _)
  apply (Booleans.holds_ofProp _ _).mpr
  change ∀ (x : Value.{u}) env, x.mem (.set (SetData.enum [Value.tuple [t, f], Value.tuple [t, t, f], f])) →
    (x.untuple 2).map (withWitnesses (fun _ => Value.set (SetData.enum [])) [0, 1]) = some env →
    ∀ (y : Value.{u}) next, y.mem (.set (SetData.enum [f])) → some (withWitness env 2 y) = some next →
      policy.booleans.holds (policy.booleans.ofProp (next 1 = next 2))
  intro x env hx henv
  simp only [Value.mem_set, SetData.mem_enum, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · rw [show (Value.tuple [t, f]).untuple 2 = some [t, f] from Value.untuple_tuple [t, f]] at henv
    cases henv
    intro y next hy hnext
    simp only [Value.mem_set, SetData.mem_enum, List.mem_singleton] at hy
    cases hy
    cases hnext
    exact (Booleans.holds_ofProp _ _).mpr rfl
  · simp [untuple_wrong_length.{u} (xs := [t, t, f]) (arity := 2) (by decide)] at henv
  · simp [untuple_boolean] at henv

private theorem tuple_exists (state : Valuation Value.{u}) :
    atState policy invalid existsExpr state = f := by
  change policy.booleans.ofProp _ = policy.booleans.falseValue
  apply ite_eq_right
  change ¬ ∃ (x : Value.{u}) (env : Nat → Value.{u}), x.mem (.set (SetData.enum [Value.tuple [f, t], f])) ∧
    (x.untuple 1).map (withWitnesses (fun _ => Value.set (SetData.enum [])) [0]) = some env ∧ _
  simp only [Value.mem_set, SetData.mem_enum, List.mem_cons, List.not_mem_nil, or_false]
  rintro ⟨x, env, rfl | rfl, he, _⟩
  · simp [untuple_wrong_length.{u} (xs := [f, t]) (arity := 1) (by decide)] at he
  · simp [untuple_boolean] at he

private theorem tuple_filter (state : Valuation Value.{u}) :
    atState policy invalid filterExpr state = .set (SetData.enum [Value.tuple [t]]) := by
  let bound := SetData.enum [Value.tuple [t], Value.tuple [f], Value.tuple [t, f], t]
  simp only [atState, CheckedExpr.eval, filterExpr, Term.eval, Term.evalBounds, Term.evalList,
    Operations.collection, Operations.base, Tagged.Policy.collectionOperations, Tagged.Policy.operations,
    Tagged.Policy.booleans, cast_eq, Bool.false_eq_true, ite_true, ite_false, Value.asSet_set]
  apply congrArg Value.set
  apply SetData.ext
  intro key
  rw [SetData.mem_sep]
  change bound.mem key ∧ (∃ env, (key.untuple 1).map (withWitnesses (fun _ => Value.set (SetData.enum [])) [0]) = some env ∧ env 0 = t) ↔ _
  simp only [bound, SetData.mem_enum, List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro ⟨rfl | rfl | rfl | rfl, env, he, hv⟩
    · rfl
    · rw [show (Value.tuple [f]).untuple 1 = some [f] from Value.untuple_tuple [f]] at he
      cases he
      exact (Bool.false_ne_true (Value.boolean_injective hv)).elim
    · simp [untuple_wrong_length.{u} (xs := [t, f]) (arity := 1) (by decide)] at he
    · simp [untuple_boolean] at he
  · rintro rfl
    exact ⟨.inl rfl, _, by rw [show (Value.tuple [t]).untuple 1 = some [t] from Value.untuple_tuple [t]]; rfl, rfl⟩

private theorem tuple_choose (state : Valuation Value.{u}) :
    atState policy invalid chooseExpr state = Value.tuple [t, f] := by
  let predicate (x : Value.{u}) := x.mem (.set (SetData.enum [Value.tuple [t, f], t])) ∧ ∃ env,
    (x.untuple 2).map (withWitnesses (fun _ => Value.set (SetData.enum [])) [0, 1]) = some env ∧ env 0 = t
  change policy.choice.choose predicate = _
  have witness : predicate (Value.tuple [t, f]) := by
    refine ⟨by simp, withWitnesses (fun _ => .set (SetData.enum [])) [0, 1] [t, f], ?_, rfl⟩
    rw [show (Value.tuple [t, f]).untuple 2 = some [t, f] from Value.untuple_tuple [t, f]]
    rfl
  obtain ⟨hm, env, he, _⟩ := policy.choice.witness ⟨_, witness⟩
  simp only [Value.mem_set, SetData.mem_enum, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with h | h
  · exact h
  · simp [h, untuple_boolean] at he

private theorem tuple_choose_without_witness (state : Valuation Value.{u}) :
    atState policy invalid chooseNone state = policy.choice.noWitness := by
  change policy.choice.choose _ = _
  apply Data.ChoicePolicy.choose_of_no_witness
  change ¬ ∃ (x : Value.{u}), x.mem (.set (SetData.enum [Value.tuple [t, f], t])) ∧ ∃ env,
    (x.untuple 1).map (withWitnesses (fun _ => Value.set (SetData.enum [])) [0]) = some env ∧ _
  simp only [Value.mem_set, SetData.mem_enum, List.mem_cons, List.not_mem_nil, or_false]
  rintro ⟨x, rfl | rfl, env, h, _⟩
  · simp [untuple_wrong_length.{u} (xs := [t, f]) (arity := 1) (by decide)] at h
  · simp [untuple_boolean] at h

private theorem unbounded_tuple_choose (state : Valuation Value.{u}) :
    atState policy invalid chooseUnbounded state = Value.tuple [t] := by
  change policy.choice.choose _ = _
  rw [show policy.choice.choose _ = policy.choice.choose (fun x => x = Value.tuple [t]) from
    Data.ChoicePolicy.congr _ (fun x => by
      change (True ∧ ∃ env, (x.untuple 1).map (withWitnesses (fun _ => Value.set (SetData.enum [])) [0]) = some env ∧
        policy.booleans.holds (policy.booleans.ofProp (env 0 = t))) ↔ _
      rw [true_and]
      constructor
      · rintro ⟨env, he, ht⟩
        obtain ⟨xs, hx, rfl⟩ := Option.map_eq_some_iff.mp he
        obtain ⟨hlen, rfl⟩ := Value.untuple_eq_some.mp hx
        match xs with
        | [value] =>
          have h : value = t := (Booleans.holds_ofProp _ _).mp ht
          rw [h]
        | [] | _ :: _ :: _ => simp at hlen
      · rintro rfl
        refine ⟨_, by rw [show (Value.tuple [t]).untuple 1 = some [t] from Value.untuple_tuple [t]]; rfl, ?_⟩
        exact (Booleans.holds_ofProp _ _).mpr rfl)]
  exact policy.choice.witness (p := fun x => x = Value.tuple [t]) ⟨_, rfl⟩

private theorem malformed_product (state : Valuation Value.{u}) :
    atState policy invalid badProduct state = invalid (.binderBounds .function [Value.set boolSet, f]) := by
  have product : Value.cartesian [.set boolSet, .set boolSet, Value.boolean false] = none := by
    simp [Value.cartesian, List.mapM_cons]
  simp only [atState, CheckedExpr.eval, badProduct, Term.eval, Term.evalBounds,
    Operations.collection, BinderMap.eval, Bounded.axes, Tagged.Policy.collectionOperations,
    Tagged.Policy.operations, Tagged.Policy.booleans, cast_eq, List.flatMap_cons, List.flatMap_nil,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append, Bool.false_eq_true, ite_false,
    show SetData.enum [t, f] = boolSet from rfl]
  rw [product]

private theorem empty_product (state : Valuation Value.{u}) :
    Value.domain policy.numeric (atState policy invalid emptyProduct state) = .set .empty := by
  simp only [atState, CheckedExpr.eval, emptyProduct, Term.eval, Term.evalBounds, Term.evalList,
    Operations.collection, BinderMap.eval, Bounded.axes, Tagged.Policy.collectionOperations,
    Tagged.Policy.operations, Tagged.Policy.booleans, List.flatMap_cons, List.flatMap_nil,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append, cast_eq,
    show SetData.enum [t, f] = boolSet from rfl, cartesian_values, Value.asSet_set, Value.domain_function,
    Graph.domain_ofFn]
  apply congrArg Value.set
  apply SetData.ext
  intro key
  rw [SetData.mem_cartesian]
  simp only [SetData.empty, SetData.mem, ZFSet.notMem_empty, iff_false]
  rintro ⟨xs, h, _⟩
  have hlen : xs.length = 3 := h.length_eq
  have hh := h.get (i := 2) (by omega) (by decide)
  exact ZFSet.notMem_empty _ hh

end Silmaril.Logic.Temporal.TLA.DataElab.Collections.Examples
