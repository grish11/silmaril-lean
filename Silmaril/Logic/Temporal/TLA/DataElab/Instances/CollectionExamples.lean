module

import all Silmaril.Logic.Temporal.TLA.DataElab.Collections.Defs
import all Silmaril.Logic.Temporal.TLA.DataElab.Defs
import Silmaril.Logic.Temporal.TLA.DataElab.Collections.Tagged
import Silmaril.Logic.Temporal.TLA.DataElab.Instances.Defs
import Silmaril.Logic.Temporal.TLA.Data.Tagged.Collections.Thms
import Silmaril.Logic.Temporal.TLA.Data.Tagged.Except.Thms
public import Silmaril.Logic.Temporal.TLA.Resolution.Names
public import Lean
meta import Silmaril.Logic.Temporal.TLA.DataElab.Instances.Defs
meta import Silmaril.Logic.Temporal.TLA.Surface.Parser.Defs
public meta import Lean

/-! Parsed named and anonymous collection calls, with checked valuation equations. -/

namespace Silmaril.Logic.Temporal.TLA.DataElab.Instances.CollectionExamples

open Resolution Data.Tagged

private meta def signature : ExternalSignature := fun _ => none

meta section

private def registry (extra : String) : Except String Registry := do
  let parse := fun source => (Surface.Parser.parseModule source).mapError reprStr
  let shared ← parse "---- MODULE Shared ----\nVARIABLE x, y\n===="
  let leaf ← parse "---- MODULE Leaf ----
EXTENDS Shared
CONSTANT Keys
LOCAL Read == x
Build == [k \\in Keys |-> <<Read, y, k>>]
ReadAt(key) == Build[key]
Update(key) == [Build EXCEPT ![key] = <<@, Read'>>][key]
Next == Read'
===="
  let root ← parse ("---- MODULE Root ----
EXTENDS Shared
CONSTANT Fixed
VARIABLE k
LOCAL Named(p) == INSTANCE Leaf WITH Keys <- {TRUE}, x <- p.payload, y <- x
INSTANCE Leaf WITH Keys <- {TRUE}, x <- y, y <- x
Graph == Build
NamedRead == Named([payload |-> <<k, Fixed>>])!ReadAt(TRUE)
Shifted == NamedRead'
Updated == Update(TRUE)
" ++ extra ++ "\n====")
  return [("shared", .parsed shared []), ("leaf", .parsed leaf [("Shared", "shared")]),
    ("root", .parsed root [("Shared", "shared"), ("Leaf", "leaf")])]

private def check (extra : String := "") : Except String Resolution.Instances.CheckedInstances := do
  (Resolution.Instances.check (← registry extra) "root").mapError reprStr

private def select (checked : Resolution.Instances.CheckedInstances) (name : String) :
    Except String BindingId := do
  let some binding := (checked.registry.moduleAt "root").bind (·.bindingAt (.ident name))
    | throw s!"Missing root binding {name}"
  return binding.id

-- A graph form remains outside core replay even when its binding passed level checking.
#guard (do
  let checked ← check
  let id ← select checked "Graph"
  return match lowerState checked signature 96 id with
    | .error (.lowering d) => d.site = ⟨"leaf", [.unit 2, .body]⟩ ∧ d.kind = .unsupported .function
    | _ => false : Except String Bool) == .ok true

#guard (do
  let checked ← check
  let id ← select checked "Shifted"
  return match lowerCollectionState checked signature 96 id with
    | .error (.wrongLevel site .state .action) => site = ⟨"root", [.unit 6, .body]⟩
    | _ => false : Except String Bool) == .ok true

-- The variable replacement's level ceiling applies through the record field read.
#guard match registry "Bad == Named([payload |-> k'])!Next" with
  | .ok input => match Resolution.Instances.check input "root" with
    | .error (.levels ⟨site, .failedRequirement requirement⟩) =>
      site = ⟨"root", [.unit 8, .body]⟩ ∧ requirement.origin = ⟨"root", [.unit 2, .substitution 1]⟩ ∧
        requirement.condition = .atMost (.fixed .action) .state
    | _ => false
  | .error _ => false

-- The host @ is lexically valid, but expanding WITH under Leaf's prime would shift it.
#guard (do
  let checked ← check "Bad == [[key |-> x] EXCEPT !.key = Named([payload |-> @])!Next]"
  let id ← select checked "Bad"
  return match lowerCollectionAction checked signature 96 id with
    | .error (.lowering d) => d.site = ⟨"leaf", [.unit 5, .body]⟩ ∧ d.kind = .primeCrossesOldValue
    | _ => false : Except String Bool) == .ok true

open Lean

deriving instance ToExpr for Resolution.Fixity
deriving instance ToExpr for Resolution.Name
deriving instance ToExpr for Step
deriving instance ToExpr for Site
deriving instance ToExpr for BindingId

-- Quote the actual expansion so that Lean checks the equations on exactly its term.
private partial def quoteTerm (term : Term signature .collections) : Elab.Term.TermElabM Lean.Expr := do
  let fragment := mkConst ``Fragment.collections
  let initial := fun ctor => mkApp2 (mkConst ctor) (mkConst ``signature) fragment
  let type := initial ``Term
  let node := fun ctor args => mkAppN (initial ctor) args
  let enabled ← Meta.mkEqRefl fragment
  let terms := fun values => do Meta.mkListLit type (← values.mapM quoteTerm)
  match term with
  | .rigid id => return node ``Term.rigid #[toExpr id]
  | .flexible id => return node ``Term.flexible #[toExpr id]
  | .witness slot => return node ``Term.witness #[toExpr slot]
  | .boolean b => return node ``Term.boolean #[toExpr b]
  | .prime site arg => return node ``Term.prime #[toExpr site, ← quoteTerm arg]
  | .enum values => return node ``Term.enum #[← terms values]
  | .function _ site binder slot domain body =>
    return node ``Term.function #[enabled, toExpr site, toExpr binder, toExpr slot,
      ← quoteTerm domain, ← quoteTerm body]
  | .record _ site fields =>
    let fieldType ← Meta.mkAppM ``Prod #[mkConst ``String, type]
    let fields ← fields.mapM fun (name, value) => do Meta.mkAppM ``Prod.mk #[toExpr name, ← quoteTerm value]
    return node ``Term.record #[enabled, toExpr site, ← Meta.mkListLit fieldType fields]
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
  | other => throwError "unexpected INSTANCE expansion: {reprStr other}"

private def emit (name : String) (action : Bool := false) : Elab.Term.TermElabM Lean.Expr := do
  let expand : Except String (CheckedExpr signature .collections) := do
    let checked ← check
    let id ← select checked name
    if action then
      return (← (lowerCollectionAction checked signature 96 id).mapError reprStr).expression
    else lowerCollectionState checked signature 96 id |>.mapError reprStr
  let checked ← ofExcept expand
  let sig := mkConst ``signature
  let value := mkApp4 (mkConst ``CheckedExpr.mk) sig (mkConst ``Fragment.collections)
    (← quoteTerm checked.term) (← Meta.mkEqRefl (toExpr true))
  return if action then mkApp2 (mkConst ``Collections.CheckedAction.mk) sig value else value

end

private noncomputable def graph : CheckedExpr signature .collections := by_elab emit "Graph"
private noncomputable def namedRead : CheckedExpr signature .collections := by_elab emit "NamedRead"
private noncomputable def shifted : Collections.CheckedAction signature := by_elab emit "Shifted" true
private noncomputable def updated : Collections.CheckedAction signature := by_elab emit "Updated" true

universe u

private def noExternal : ExternalInterpretation Value.{u} signature :=
  fun _ _ impossible => nomatch impossible

private def x : BindingId := .declared ⟨"shared", [.unit 0, .member 0]⟩
private def y : BindingId := .declared ⟨"shared", [.unit 0, .member 1]⟩
private def k : BindingId := .declared ⟨"root", [.unit 1, .member 0]⟩
private def fixed : BindingId := .declared ⟨"root", [.unit 0, .member 0]⟩
private def key : Value.{u} := .boolean true
private def keys : SetData.{u} := SetData.enum [key]

variable (policy : Tagged.Policy.{u}) (invalid : Tagged.CollectionPolicy.{u})

private theorem anonymous_graph_eq (v : Valuation Value.{u}) :
    graph.eval (policy.collectionOperations invalid) policy.booleans noExternal v =
      .function (Graph.ofFn keys fun w => .tuple [v.flexible y, v.flexible x, w]) := by
  simp [CheckedExpr.eval, graph, Term.eval, Term.evalList, Operations.collection, Operations.base,
    Tagged.Policy.collectionOperations, Tagged.Policy.operations, Tagged.Policy.booleans,
    keys, key, x, y, withWitness]

private theorem named_read_eq (v : Valuation Value.{u}) :
    namedRead.eval (policy.collectionOperations invalid) policy.booleans noExternal v =
      .tuple [.tuple [v.flexible k, v.rigid fixed], v.flexible x, key] := by
  let payload := Value.tuple [v.flexible k, v.rigid fixed]
  let fields := [("payload", payload)]
  let body := fun field => (fields.lookup field).getD (invalid (.record fields))
  have payloadEq : Value.apply policy.numeric (.record ["payload"] body) (.string "payload") =
      payload := Value.apply_function _ (Graph.lookup_eq_some.mp (Graph.lookup_record body (by simp)))
  simp [CheckedExpr.eval, namedRead, Term.eval, Term.evalList, Term.evalFields,
    Operations.collection, Operations.base, Tagged.Policy.collectionOperations, Tagged.Policy.operations,
    Tagged.Policy.booleans, withWitness]
  change Value.apply policy.numeric
    (.function (Graph.ofFn keys fun w => .tuple
      [Value.apply policy.numeric (.record ["payload"] body) (.string "payload"), v.flexible x, w])) key = _
  rw [payloadEq]
  exact Value.apply_function _ (Graph.lookup_eq_some.mp (Graph.lookup_ofFn (by simp [keys, SetData.mem_enum])))

private theorem shifted_eq (v : Endpoints.EndpointValuation Value.{u}) :
    shifted.eval (policy.collectionOperations invalid) policy.booleans noExternal v =
      .tuple [.tuple [v.target k, v.rigid fixed], v.target x, key] :=
  named_read_eq policy invalid ⟨v.rigid, v.target⟩

private theorem updated_eq (v : Endpoints.EndpointValuation Value.{u}) :
    updated.eval (policy.collectionOperations invalid) policy.booleans noExternal v =
      .tuple [.tuple [v.source y, v.source x, key], v.target y] := by
  let g := Graph.ofFn keys (fun k => Value.tuple [v.source y, v.source x, k])
  have mem : g.domain.mem key := by simp [g, keys, SetData.mem_enum]
  simp [Collections.CheckedAction.eval, updated, Term.eval, Term.evalList, Term.evalClauses,
    Operations.collection, Tagged.Policy.collectionOperations, Tagged.Policy.operations,
    Tagged.Policy.booleans, withWitness]
  change Value.apply policy.numeric (Value.updatePath policy.numeric (.function g) [key]
    (fun old => .tuple [old, v.target y])) key = _
  rw [Value.updatePath_single, Value.update_function]
  apply Value.apply_function
  apply Graph.lookup_eq_some.mp
  rw [Graph.lookup_update mem]
  have found : g.lookup key = some (.tuple [v.source y, v.source x, key]) :=
    Graph.lookup_ofFn (show keys.mem key by simpa [g] using mem)
  rw [Value.apply_function _ (Graph.lookup_eq_some.mp found)]

end Silmaril.Logic.Temporal.TLA.DataElab.Instances.CollectionExamples
