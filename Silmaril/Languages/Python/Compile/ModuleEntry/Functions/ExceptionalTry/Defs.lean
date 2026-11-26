module

public import Silmaril.Languages.Python.Compile.ModuleEntry.Defs

/-! # Reached completion and cleanup for checked module suites -/

@[expose] public section
namespace Silmaril.Languages.Python.Compile.ModuleEntry.Functions.ExceptionalTry

structure Plan (action : Type) where
  body : List action
  handler : Option (List action)
  otherwise : List action
  cleanup : List action

structure Outcome (state failure : Type) where
  reached : state
  completion : Except failure Unit

def Outcome.canEnterCleanup {state failure : Type} (outcome : Outcome state failure)
    (isPythonError : failure → Bool) : Bool :=
  match outcome.completion with
  | .ok () => true
  | .error failure => isPythonError failure

/-- Normal cleanup preserves the pending completion. A cleanup error takes
precedence with the state reached by that cleanup. -/
def Outcome.afterCleanup {state failure : Type} (pending cleaned : Outcome state failure) :
    Outcome state failure :=
  match cleaned.completion with
  | .ok () => ⟨cleaned.reached, pending.completion⟩
  | .error _ => cleaned

def afterBody {state failure action : Type} (suite : state → List action → Outcome state failure)
    (isPythonError : failure → Bool) (body : Outcome state failure) (handler : Option (List action))
    (otherwise : List action) : Outcome state failure :=
  match body.completion, handler with
  | .ok (), _ => suite body.reached otherwise
  | .error failure, some arm => if isPythonError failure then suite body.reached arm else body
  | .error _, none => body

def runCleanup {state failure action : Type} (suite : state → List action → Outcome state failure)
    (isPythonError : failure → Bool) (pending : Outcome state failure)
    (cleanup : List action) : Outcome state failure :=
  if pending.canEnterCleanup isPythonError then
    pending.afterCleanup (suite pending.reached cleanup)
  else pending

def run {state failure action : Type} (suite : state → List action → Outcome state failure)
    (isPythonError : failure → Bool) (initial : state) (plan : Plan action) : Outcome state failure :=
  let body := suite initial plan.body
  let pending := afterBody suite isPythonError body plan.handler plan.otherwise
  runCleanup suite isPythonError pending plan.cleanup

open Source (ExceptHandler Expr Scope Stmt)

def scalarAtom : Expr → Bool
  | .name _ => true
  | source => (exactScalarLiteral? source).isSome

def scalarStatement : Stmt → Bool
  | .pass => true
  | .assert_ condition none => scalarAtom condition
  | statement =>
    match binding? statement with
    | some checked => scalarAtom checked.val.2
    | none => false

inductive Suite (scope : Scope) : List Stmt → List (Action scope) → Prop where
  | scalar {source actions} (allowed : source.all scalarStatement = true)
      (code : ModuleEntry.Translation scope source actions) :
      Suite scope source (actions.map Action.inLiteralArm)

def suite? (scope : Scope) (source : List Stmt) : Option {actions // Suite scope source actions} := do
  if allowed : source.all scalarStatement = true then
    let lowered ← (lowerStatements scope source).toOption
    return ⟨lowered.val.map Action.inLiteralArm, .scalar allowed lowered.property⟩
  else none

inductive Handler (scope : Scope) : List ExceptHandler → List Stmt → List Stmt →
    Option (List (Action scope)) → Prop where
  | finallyOnly {cleanup} (present : cleanup.isEmpty = false) :
      Handler scope [] [] cleanup none
  | bare {source otherwise cleanup actions} (present : source.isEmpty = false)
      (translated : Suite scope source actions) :
      Handler scope [⟨none, none, source⟩] otherwise cleanup (some actions)

def handler? (scope : Scope) : (handlers : List ExceptHandler) → (otherwise cleanup : List Stmt) →
    Option {handler // Handler scope handlers otherwise cleanup handler}
  | [], [], cleanup =>
    if present : cleanup.isEmpty = false then some ⟨none, .finallyOnly present⟩ else none
  | [⟨none, none, source⟩], _, _ =>
    if present : source.isEmpty = false then
      (suite? scope source).map fun checked => ⟨some checked.val, .bare present checked.property⟩
    else none
  | _, _, _ => none

inductive Translation (scope : Scope) : Stmt → Plan (Action scope) → Prop where
  | checked {body handlers otherwise cleanup first handler normal final}
      (present : body.isEmpty = false) (bodyCode : Suite scope body first)
      (handlerCode : Handler scope handlers otherwise cleanup handler)
      (elseCode : Suite scope otherwise normal) (cleanupCode : Suite scope cleanup final) :
      Translation scope (.try_ body handlers otherwise cleanup) ⟨first, handler, normal, final⟩

def check (scope : Scope) : (source : Stmt) → Option {plan // Translation scope source plan}
  | .try_ body handlers otherwise cleanup =>
    if present : body.isEmpty = false then do
      let first ← suite? scope body
      let handler ← handler? scope handlers otherwise cleanup
      let normal ← suite? scope otherwise
      let final ← suite? scope cleanup
      return ⟨⟨first.val, handler.val, normal.val, final.val⟩,
        .checked present first.property handler.property normal.property final.property⟩
    else none
  | _ => none

end Silmaril.Languages.Python.Compile.ModuleEntry.Functions.ExceptionalTry
