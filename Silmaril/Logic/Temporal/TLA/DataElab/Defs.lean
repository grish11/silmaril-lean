module

public import Silmaril.Logic.Temporal.TLA.DataElab.Semantics

/-!
# Checked lowering for TLA+ data expressions

Expand a nullary source definition using resolver identities. An expression
actual is an expanded term, and an operator actual retains its lexical context.
See `docs/projects/tla-data-elab.md` for the supported surface and contracts.
-/

namespace Silmaril.Logic.Temporal.TLA.DataElab

open Resolution

universe u

public section

inductive Unsupported where
  | literal | cartesian | caseExpression | tupleBinder | setMapBounds
  | function | functionSet | index | tuple | record | recordSet | field
  | except | actionOrTemporal | proofOrQualifiedReference | labeled | letDeclaration
  deriving DecidableEq, Repr

inductive DiagnosticKind where
  | expectedNullaryDefinition (id : BindingId)
  | missingReference (role : ReferenceRole)
  | missingBinding (id : BindingId)
  | unavailableDefinition (id : BindingId)
  | missingLexicalBinding (id : BindingId)
  | invalidApplication (id : BindingId)
  | missingPrimitive (id : BindingId)
  | primitiveArity (id : BindingId) (expected registered : Nat)
  | unsupportedPrimitiveSignature (id : BindingId)
  | unsupportedBuiltin (id : BindingId)
  | unsupported (form : Unsupported)
  | primeRequiresLevels
  | nestedPrime (inner : Site)
  | expansionLimit
  | invalidExpansion
  deriving DecidableEq, Repr

structure Diagnostic where
  site : Site
  kind : DiagnosticKind
  deriving DecidableEq, Repr

/-- A lowered expression. Its expanded syntax is available to subsequent passes. -/
structure CheckedExpr (signature : ExternalSignature) where
  private mk ::
  term : Term signature
  wellFormed : term.isWellFormed [] = true

/-- Interpret a checked expression at one valuation. Witness reads use the slots
introduced by enclosing binders. No state transition is inferred here. -/
@[expose] noncomputable def CheckedExpr.eval {V : Type u} {signature : ExternalSignature}
    (expression : CheckedExpr signature) (ops : DataOperations V) (B : Booleans V)
    (external : ExternalInterpretation V signature) (valuation : Valuation V) : V :=
  expression.term.eval ops B external valuation (fun _ => ops.enum [])

end

variable {signature : ExternalSignature}

private abbrev LowerM := StateT Nat (Except Diagnostic)

private def fail {α : Type} (site : Site) (kind : DiagnosticKind) : LowerM α :=
  throw ⟨site, kind⟩

private def freshWitness : LowerM Nat := do
  let slot ← get
  set (slot + 1)
  return slot

private inductive Local (signature : ExternalSignature) where
  | expression (term : Term signature)
  | closure (home : Site) (body : Surface.Expr) (captured : List (BindingId × Local signature))
  | named (binding : Binding)

private abbrev Context (signature : ExternalSignature) := List (BindingId × Local signature)

private abbrev Visit (signature : ExternalSignature) :=
  Context signature → Site → Surface.Expr → LowerM (Term signature)

private def declarationId (site : Site) (step : Step) : BindingId := .declared (site.child step)

private def sourceBody (source : Surface.Module) (path : Path) : Option Surface.Expr := do
  let [.unit index] := path | none
  let .definition (.operator _ _ body) ← source.units[index]? | none
  return body

private def useBinding (registry : CheckedRegistry) (site : Site) (role : ReferenceRole)
    (allowPrime : Bool := false) : LowerM Binding := do
  let some reference := (registry.moduleAt site.moduleId).bind (·.referenceAt site.path)
    | fail site (.missingReference role)
  unless reference.role = role do fail site (.missingReference role)
  if !allowPrime && reference.target = .builtin (.symbol .postfix "'") then
    fail site .primeRequiresLevels
  let some binding := registry.findBinding reference.target
    | fail site (.missingBinding reference.target)
  return binding

private def lowerBuiltin (site : Site) (name : Name) (args : List (Term signature)) :
    LowerM (Term signature) :=
  match name, args with
  | .symbol .postfix "'", [operand] =>
    match operand.firstPrime with
    | some inner => fail site (.nestedPrime inner)
    | none => pure (.prime site operand)
  | .ident "TRUE", [] => pure (.boolean true)
  | .ident "FALSE", [] => pure (.boolean false)
  | .ident "BOOLEAN", [] => pure .booleanSet
  | .symbol .prefix "\\lnot", [arg] => pure (.not arg)
  | .symbol .infix "=", [l, r] => pure (.eq false l r)
  | .symbol .infix "/=", [l, r] => pure (.eq true l r)
  | .symbol .infix "\\in", [l, r] => pure (.mem false l r)
  | .symbol .infix "\\notin", [l, r] => pure (.mem true l r)
  | .symbol .infix "\\land", [l, r] => pure (.logic .and l r)
  | .symbol .infix "\\lor", [l, r] => pure (.logic .or l r)
  | .symbol .infix "=>", [l, r] => pure (.logic .implies l r)
  | .symbol .infix "\\equiv", [l, r] => pure (.logic .equiv l r)
  | _, _ => fail site (.unsupportedBuiltin (.builtin name))

private def expressionArgs (site : Site) (id : BindingId) (args : List (Local signature)) :
    LowerM (List (Term signature)) :=
  args.mapM fun arg =>
    match arg with
    | .expression term => pure term
    | _ => fail site (.invalidApplication id)

private def lowerPrimitive (site : Site) (binding : Binding) (args : List (Local signature)) :
    LowerM (Term signature) := do
  unless binding.slots = List.replicate binding.slots.length .expression do
    fail site (.unsupportedPrimitiveSignature binding.id)
  let terms ← expressionArgs site binding.id args
  if admitted : signature binding.id = some terms.length then
    return .external binding.id terms.length admitted terms
  else
    match signature binding.id with
    | none => fail site (.missingPrimitive binding.id)
    | some arity => fail site (.primitiveArity binding.id terms.length arity)

private def applyClosure (visit : Visit signature) (home : Site) (body : Surface.Expr)
    (captured : Context signature) (args : List (Local signature)) : LowerM (Term signature) :=
  let formals := args.zipIdx.map fun (arg, i) => (declarationId home (.parameter i), arg)
  visit (formals ++ captured) (home.child .body) body

private def applyGlobal (registry : CheckedRegistry) (visit : Visit signature)
    (site : Site) (binding : Binding) (args : List (Local signature)) : LowerM (Term signature) := do
  match binding.id with
  | .builtin name => lowerBuiltin site name (← expressionArgs site binding.id args)
  | .declared home =>
    match binding.kind with
    | .constant =>
      if args.isEmpty && (signature binding.id).isNone then
        pure (.rigid binding.id)
      else lowerPrimitive site binding args
    | .variable =>
      if args.isEmpty then pure (.flexible binding.id) else fail site (.invalidApplication binding.id)
    | .operator =>
      let some mod := registry.moduleAt home.moduleId
        | fail site (.unavailableDefinition binding.id)
      match mod.source with
      | none => lowerPrimitive site binding args
      | some source =>
        let some body := sourceBody source home.path | fail site (.unavailableDefinition binding.id)
        applyClosure visit home body [] args
    | _ => fail site (.missingLexicalBinding binding.id)

private def applyBinding (registry : CheckedRegistry) (visit : Visit signature)
    (locals : Context signature) (site : Site) (binding : Binding) (args : List (Local signature)) :
    LowerM (Term signature) :=
  match locals.lookup binding.id with
  | some (.expression term) =>
    if args.isEmpty then pure term else fail site (.invalidApplication binding.id)
  | some (.closure home body captured) => applyClosure visit home body captured args
  | some (.named target) => applyGlobal registry visit site target args
  | none => applyGlobal registry visit site binding args

private def lowerActual (registry : CheckedRegistry) (visit : Visit signature)
    (locals : Context signature) (site : Site) (slot : Slot) (arg : Surface.OpArg) :
    LowerM (Local signature) := do
  match slot, arg with
  | .expression, .expr body => return .expression (← visit locals site body)
  | .expression, _ => fail site (.missingReference .application)
  | .operator _, .lambda _ body => return .closure site body locals
  | .operator _, _ =>
    let binding ← useBinding registry site .operatorArgument
    match locals.lookup binding.id with
    | some actual => return actual
    | none =>
      if binding.kind = .formal then fail site (.missingLexicalBinding binding.id)
      return .named binding

private def lowerApplication (registry : CheckedRegistry) (visit : Visit signature)
    (locals : Context signature) (site : Site) (args : List Surface.OpArg) (child : Nat → Step)
    (allowPrime : Bool) : LowerM (Term signature) := do
  let binding ← useBinding registry site .application allowPrime
  unless args.length = binding.slots.length do fail site (.invalidApplication binding.id)
  let actuals ← (binding.slots.zip args).zipIdx.mapM fun ((slot, arg), i) =>
    lowerActual registry visit locals (site.child (child i)) slot arg
  applyBinding registry visit locals site binding actuals

private def bindWitness (site : Site) (index : Nat) (locals : Context signature) :
    LowerM (Nat × Context signature) := do
  let slot ← freshWitness
  return (slot, (declarationId site (.binder index), .expression (.witness slot)) :: locals)

private def lowerQuant (visit : Visit signature) (locals : Context signature)
    (site : Site) (kind : Surface.Quantifier) (binders : Surface.RigidBinders)
    (body : Surface.Expr) : LowerM (Term signature) := do
  let groups ← match binders with
    | .unbounded names => pure [(site, names, none)]
    | .bounded groups =>
      groups.zipIdx.mapM fun (group, i) => do
        let groupSite := site.child (.bound i)
        match group.names with
        | .tuple _ => fail groupSite (.unsupported .tupleBinder)
        | .names names => pure (groupSite, names, some (← visit locals (groupSite.child .domain)
            group.domain))
  let (inner, reversed) ← groups.foldlM (init := (locals, [])) fun (inner, slots)
      (groupSite, names, domain) =>
    names.zipIdx.foldlM (init := (inner, slots)) fun (inner, slots) (_, index) => do
      let (slot, inner) ← bindWitness groupSite index inner
      return (inner, (slot, domain) :: slots)
  let result ← visit inner (site.child .body) body
  return reversed.foldl (fun term (slot, domain) => .quant kind slot domain term) result

private def lower (registry : CheckedRegistry) (allowPrime : Bool) (fuel : Nat)
    (locals : Context signature)
    (site : Site) (expr : Surface.Expr) : LowerM (Term signature) := do
  match fuel with
  | 0 => fail site .expansionLimit
  | remaining + 1 =>
    let visit := lower registry allowPrime remaining
    let operands := fun (items : List Surface.Expr) =>
      items.zipIdx.mapM fun (item, i) => visit locals (site.child (.operand i)) item
    let symbolic := fun args =>
      lowerApplication registry visit locals site (args.map Surface.OpArg.expr) .operand allowPrime
    let unsupported := fun form => fail site (.unsupported form)
    match expr with
    | .ref (.operator _) args [] => lowerApplication registry visit locals site args .argument allowPrime
    | .ref .. => unsupported .proofOrQualifiedReference
    | .prefix _ arg | .postfix _ arg => symbolic [arg]
    | .infix _ left right => symbolic [left, right]
    | .ifThenElse condition yes no =>
      return .ite (← visit locals (site.child (.operand 0)) condition)
        (← visit locals (site.child (.operand 1)) yes) (← visit locals (site.child (.operand 2)) no)
    | .junction kind items => return .junction kind (← operands items)
    | .letIn declarations body =>
      let inner ← declarations.zipIdx.foldlM (init := locals) fun context (decl, i) => do
        let home := site.child (.letDecl i)
        match decl with
        | .definition (.operator _ _ body) =>
          return (.declared home, .closure home body context) :: context
        | _ => fail home (.unsupported .letDeclaration)
      visit inner (site.child .body) body
    | .rigidQuant kind binders body => lowerQuant visit locals site kind binders body
    | .choose (.ident _) domain body =>
      let bound ← domain.mapM (visit locals (site.child .domain))
      let (slot, inner) ← bindWitness site 0 locals
      return .choose slot bound (← visit inner (site.child .body) body)
    | .setFilter (.ident _) domain body =>
      let bound ← visit locals (site.child .domain) domain
      let (slot, inner) ← bindWitness site 0 locals
      return .filter slot bound (← visit inner (site.child .body) body)
    | .choose .. | .setFilter .. => unsupported .tupleBinder
    | .setMap body [⟨.names [_], domain⟩] =>
      let groupSite := site.child (.bound 0)
      let bound ← visit locals (groupSite.child .domain) domain
      let (slot, inner) ← bindWitness groupSite 0 locals
      return .image slot bound (← visit inner (site.child .body) body)
    | .setMap _ [⟨.tuple _, _⟩] => unsupported .tupleBinder
    | .setMap .. => unsupported .setMapBounds
    | .setEnum items => return .enum (← operands items)
    | .literal (.natural value) => pure (.numeral value)
    | .literal _ => unsupported .literal
    | .cartesian _ => unsupported .cartesian
    | .cases .. => unsupported .caseExpression
    | .function .. => unsupported .function
    | .functionSet .. => unsupported .functionSet
    | .index .. => unsupported .index
    | .tuple _ => unsupported .tuple
    | .record _ => unsupported .record
    | .recordSet _ => unsupported .recordSet
    | .field .. => unsupported .field
    | .except .. | .oldValue => unsupported .except
    | .action .. | .fairness .. | .temporalQuant .. => unsupported .actionOrTemporal
    | .labeled .. => unsupported .labeled
termination_by structural fuel

private def definitionBody (registry : CheckedRegistry) (id : BindingId) :
    Except Diagnostic (Site × Surface.Expr) := do
  let .declared home := id
    | throw ⟨⟨registry.root, []⟩, .expectedNullaryDefinition id⟩
  let body : Option Surface.Expr := do
    let binding ← registry.findBinding id
    if binding.kind = .operator ∧ binding.slots = [] then
      let mod ← registry.moduleAt home.moduleId
      let source ← mod.source
      sourceBody source home.path
    else none
  let some body := body | throw ⟨home, .expectedNullaryDefinition id⟩
  return (home, body)

private def lowerBody (registry : CheckedRegistry) (signature : ExternalSignature)
    (allowPrime : Bool) (maxDepth : Nat) (home : Site) (body : Surface.Expr) :
    Except Diagnostic (CheckedExpr signature) := do
  let (term, _) ← (lower registry allowPrime maxDepth [] (home.child .body) body).run 0
  if valid : term.isWellFormed [] = true then
    return ⟨term, valid⟩
  else
    throw ⟨home.child .body, .invalidExpansion⟩

/-- Expand a nullary source definition without a level check. Prime is
rejected. The depth bound counts visits through source expressions and expanded
bodies. Exhaustion reports the next unvisited site. -/
public def lowerDefinition (registry : CheckedRegistry) (signature : ExternalSignature)
    (maxDepth : Nat) (id : BindingId) : Except Diagnostic (CheckedExpr signature) := do
  let (home, body) ← definitionBody registry id
  lowerBody registry signature false maxDepth home body

end Silmaril.Logic.Temporal.TLA.DataElab
