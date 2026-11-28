module

public import Silmaril.Languages.Python.Compile.ModuleEntry.Defs

/-! # Module try suites with a normally completing prefix

The protected suite and else suite contain only pass and exact scalar
literal writes. They cannot transfer control or raise. The selected cleanup
uses the existing scalar actions, including their reached failures.
-/

@[expose] public section
namespace Silmaril.Languages.Python.Compile.ModuleEntry.Functions.NormalTry

open Source (ExceptHandler Name Scope Stmt)

structure Write (scope : Scope) where
  name : Name
  reference : GlobalReference scope name
  value : Core.Module.Value

def Write.action {scope : Scope} (write : Write scope) : Action scope :=
  .assign write.name write.reference (.scalarResult write.value)

inductive Suite (scope : Scope) : List Stmt → List (Write scope) → Prop where
  | nil : Suite scope [] []
  | pass {rest writes} (tail : Suite scope rest writes) :
      Suite scope (.pass :: rest) writes
  | assign {statement name source reference value rest writes}
      (binding : Binding statement name source) (literal : exactScalarLiteral? source = some value)
      (tail : Suite scope rest writes) :
      Suite scope (statement :: rest) (⟨name, reference, value⟩ :: writes)

def suite? (scope : Scope) : (body : List Stmt) → Option {writes // Suite scope body writes}
  | [] => some ⟨[], .nil⟩
  | .pass :: rest => (suite? scope rest).map fun tail => ⟨tail.val, .pass tail.property⟩
  | statement :: rest => do
    let ⟨(name, source), binding⟩ ← binding? statement
    let reference ← globalReference? scope name
    let tail ← suite? scope rest
    match literal : exactScalarLiteral? source with
    | some value => some ⟨⟨name, reference, value⟩ :: tail.val, .assign binding literal tail.property⟩
    | none => none

/-- Admit a finally-only statement or one bare handler. The skipped handler
has the same straight-line literal grammar, which excludes scope effects. -/
inductive Shape (scope : Scope) : List ExceptHandler → List Stmt → List Stmt → Prop where
  | finallyOnly {cleanup} (present : cleanup.isEmpty = false) : Shape scope [] [] cleanup
  | bare {body otherwise cleanup writes} (present : body.isEmpty = false) (checked : Suite scope body writes) :
      Shape scope [⟨none, none, body⟩] otherwise cleanup

def shape? (scope : Scope) : (handlers : List ExceptHandler) → (otherwise cleanup : List Stmt) →
    Option (PLift (Shape scope handlers otherwise cleanup))
  | [], [], cleanup =>
    if present : cleanup.isEmpty = false then some ⟨.finallyOnly present⟩ else none
  | [⟨none, none, body⟩], _, _ => do
    if present : body.isEmpty = false then
      let checked ← suite? scope body
      return ⟨.bare present checked.property⟩
    else none
  | _, _, _ => none

inductive Translation (scope : Scope) : Stmt → List (Action scope) → Prop where
  | reached {body handlers otherwise cleanup first next final}
      (present : body.isEmpty = false) (shape : Shape scope handlers otherwise cleanup)
      (protectedCode : Suite scope body first) (normal : Suite scope otherwise next)
      (cleanupShape : cleanup.all literalArmStatement = true)
      (cleanupCode : ModuleEntry.Translation scope cleanup final) :
      Translation scope (.try_ body handlers otherwise cleanup)
        ((first ++ next).map Write.action ++ final.map Action.inLiteralArm)

def check (scope : Scope) : (statement : Stmt) → Option {actions // Translation scope statement actions}
  | .try_ body handlers otherwise cleanup => do
    if present : body.isEmpty = false then
      let shape ← shape? scope handlers otherwise cleanup
      let first ← suite? scope body
      let next ← suite? scope otherwise
      if cleanupShape : cleanup.all literalArmStatement = true then
        let final ← (lowerStatements scope cleanup).toOption
        return ⟨(first.val ++ next.val).map Write.action ++ final.val.map Action.inLiteralArm,
          .reached present shape.down first.property next.property cleanupShape final.property⟩
      else none
    else none
  | _ => none

end Silmaril.Languages.Python.Compile.ModuleEntry.Functions.NormalTry
